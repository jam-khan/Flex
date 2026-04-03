import Lean

import Aesop
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Solve.Solver
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Elab.FromExpr

open Lean Elab Meta Command Tactic

private def attemptTactic (t : TacticM Unit) : TacticM Bool :=
  tryCatch (do t; pure Bool.true) (fun _ => pure Bool.false)

private def tryClosers : TacticM Bool := do
  let b ← attemptTactic (evalTactic (← `(tactic| grind)))
  match b with
  | Bool.true => pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| aesop)))
  match b with
  | Bool.true => pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| omega)))
  match b with
  | Bool.true => pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| (constructor <;> grind))))
  match b with
  | Bool.true => pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| (simp_all; grind))))
  match b with
  | Bool.true => pure Bool.true
  | Bool.false => pure Bool.false
private partial def closeLoop : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => pure ()
  | g :: restGoals =>
    let ty ← whnfR (← g.getType)
    if ty.isForall then
      evalTactic (← `(tactic| intro _))
      closeLoop
    else if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| and_intros))
      closeLoop
    else
      let closed ← tryClosers
      if closed then
        closeLoop
      else
        setGoals restGoals
        closeLoop
        let remaining ← getGoals
        setGoals (g :: remaining)

private def closeResidualGoals : TacticM Unit := do
  let goals ← getGoals
  if goals.isEmpty then pure ()
  else
    let _ ← attemptTactic (evalTactic (← `(tactic| simp_all)))
    let goals ← getGoals
    if goals.isEmpty then pure ()
    else closeLoop

elab "solve_fixpoint" : tactic => withMainContext do
  -- unfolding at top level
  let goal ← getMainGoal
  let newGoal ← goal.withContext do
    let target    ← goal.getType
    let unfolded  ← unfoldDefinition target
    goal.replaceTargetDefEq unfolded
  replaceMainGoal [newGoal]
  
  let goal ← getMainGoal
  let goalType ← goal.getType
  let reduced ← reduce goalType

  let fvarsRef ← IO.mkRef ({} : FVarMap)
  let kvarsRef ← IO.mkRef ({} : KVarSet)
  let propAST ← toPropASTWithTracking fvarsRef kvarsRef reduced
  let fvarMap ← fvarsRef.get
  let kvarSet ← kvarsRef.get
  let constraint ← toConstraint fvarMap kvarSet propAST

  let kvars := constraint.kvars.eraseDups
  let mut solutions : List (Name × Pred) := []
  let mut curr := constraint
  for κ in kvars do
    let sol := curr.sol1 κ
    solutions := solutions ++ [(κ.name, sol)]
    curr := curr.elim1 κ

  for (_κName, sol) in solutions do
    let witness ← solToWitnessExpr sol
    let witnessSyn ← PrettyPrinter.delab witness
    evalTactic (← `(tactic| refine ⟨$witnessSyn, ?_⟩))

  closeResidualGoals
