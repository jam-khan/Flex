import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Solve.Solver
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Elab.FromExpr

open Lean Elab Meta Command Tactic

private def tryTac (tac : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  let ok ← tryCatch
    (do evalTactic tac; pure Bool.true)
    (fun _ => do restoreState saved; pure Bool.false)
  return ok

elab "solve_fixpoint" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let reduced ← reduce goalType

  -- Phase 1: Reflect Prop → Constraint
  let fvarsRef ← IO.mkRef ({} : FVarMap)
  let kvarsRef ← IO.mkRef ({} : KVarSet)
  let propAST ← toPropASTWithTracking fvarsRef kvarsRef reduced
  let fvarMap ← fvarsRef.get
  let kvarSet ← kvarsRef.get
  let constraint ← toConstraint fvarMap kvarSet propAST

  -- Phase 2: Solve κ-variables
  let kvars := constraint.kvars.eraseDups
  let mut solutions : List (Name × Pred) := []
  let mut curr := constraint
  for κ in kvars do
    let sol := curr.sol1 κ
    solutions := solutions ++ [(κ.name, sol)]
    curr := curr.elim1 κ

  -- Phase 3: Instantiate outer ∃ κ with simp-simplified witnesses
  for (_κName, sol) in solutions do
    let witness ← solToWitnessExpr sol
    let simplified ← lambdaTelescope witness fun args body => do
      let (result, _) ← simp body (← Simp.Context.mkDefault)
      mkLambdaFVars args result.expr
    let fmtBefore ← ppExpr witness
    let fmtAfter ← ppExpr simplified
    logInfo m!"κ witness (raw):        {fmtBefore}"
    logInfo m!"κ witness (simplified): {fmtAfter}"
    let witnessSyn ← PrettyPrinter.delab simplified
    evalTactic (← `(tactic| refine ⟨$witnessSyn, ?_⟩))

    -- Phase 4: Beta reduce only (no rewriting)
  let _ ← tryTac (← `(tactic| dsimp only))

  -- Phase 5: Try grind on the whole thing
  if ← tryTac (← `(tactic| grind)) then return

  -- Phase 6: Intro all foralls
  let _ ← tryTac (← `(tactic| intros))

  -- Phase 7: Split conjunctions
  for _ in List.range 20 do
    if !(← tryTac (← `(tactic| constructor))) then break

  -- Phase 8: For each subgoal, split, simp, grind, try exists
  let subgoals ← getGoals
  let mut unsolved : List MVarId := []
  for g in subgoals do
    if ← g.isAssigned then continue
    setGoals [g]
    -- Intro any remaining foralls
    let _ ← tryTac (← `(tactic| intros))
    -- Split any conjunctions in this subgoal
    for _ in List.range 20 do
      if !(← tryTac (← `(tactic| constructor))) then break
    -- Now we may have new subgoals from splitting — process all of them
    let innerGoals ← getGoals
    for ig in innerGoals do
      if ← ig.isAssigned then continue
      setGoals [ig]
      let _ ← tryTac (← `(tactic| intros))
      let _ ← tryTac (← `(tactic| simp at *))
      if ← tryTac (← `(tactic| grind)) then continue
      -- Try existential witnesses
      let goal ← getMainGoal
      let goalType ← whnf (← goal.getType)
      if Expr.isAppOfArity goalType ``Exists 2 then
        let exTy ← whnf (Expr.getArg! goalType 0)
        let lctx ← getLCtx
        let mut closed := Bool.false
        for decl in lctx do
          if closed then break
          if decl.isImplementationDetail then continue
          let declTy ← whnf decl.type
          if ← isDefEq declTy exTy then
            let vSyn ← PrettyPrinter.delab (mkFVar decl.fvarId)
            if ← tryTac (← `(tactic| exists $vSyn <;> grind)) then
              closed := Bool.true
        if closed then continue
      for r in (← getGoals) do
        unsolved := unsolved ++ [r]
  setGoals unsolved
