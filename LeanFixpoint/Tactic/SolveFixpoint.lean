import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Solve.Solver
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Elab.FromExpr

open Lean Elab Meta Command Tactic

elab "solve_fixpoint" : tactic => withMainContext do
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

  -- try
  --   evalTactic (← `(tactic| simp_all))
  -- catch _ => pure ()

  -- let goals ← getGoals
  -- if !goals.isEmpty then
  --   try
  --     evalTactic (← `(tactic| first | grind | omega))
  --   catch _ => pure ()
