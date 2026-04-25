import Lean
import Aesop

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad
import LeanFixpoint.Tactic.Internal.Utils
import LeanFixpoint.Tactic.Tactics
import LeanFixpoint.Tactic.Internal.CloseLoop
import LeanFixpoint.Tactic.SplitHyps

open Lean Elab Meta Tactic

initialize Lean.registerTraceClass `solveFusion

private def closeResidualGoals : TacticM Unit := do
  let goals ← getGoals
  if goals.isEmpty then pure ()
  else
    -- Phase 1: dsimp + zap to decompose ∀/∧ and close trivial goals
    let _ ← attemptTactic (evalTactic (← `(tactic| dsimp only)))
    let _ ← attemptTactic (evalTactic (← `(tactic| zap)))
    let goals ← getGoals
    if goals.isEmpty then pure ()
    else
      -- Phase 2: split all ∨/∧/∃ in hypotheses, then simp_all + grind
      let _ ← attemptTactic (evalTactic (←
        `(tactic| all_goals (split_hyps; all_goals simp_all; all_goals grind))))
      let goals ← getGoals
      if goals.isEmpty then pure ()
      else closeLoop

/-!
  ## `solve_fusion` tactic

  Handles acyclic κ-variables via fusion (sol1 + elim1).
  No predicate abstraction, no qualifiers.
  Sufficient for Demo/Basic.lean acyclic examples.
-/
private def solveFusionImpl : TacticM Unit := withMainContext do
  let _ ← attemptTactic (evalTactic (← `(tactic| intros)))

  let goal ← getMainGoal
  let _ ← attemptTactic
    (do let newGoal ← goal.withContext do
          let target   ← goal.getType
          let unfolded ← unfoldDefinition target
          goal.replaceTargetDefEq unfolded
        replaceMainGoal [newGoal])

  let goal ← getMainGoal
  let _ ← tryCatch
    (do
      let goalType ← goal.getType
      let reduced  ← reduce goalType

      -- Phase 1-4: Run inside peelExistentials CPS (MetaM) to keep fvars alive.
      -- Compute solutions and witness Exprs, return them for Phase 5.
      let emptyKvars : Std.HashMap FVarId KVar := {}
      let witnesses : List Expr ← peelExistentials reduced emptyKvars [] fun kvarMap kvarsInOrder body => do
        let kctx : KContext := { kvars := kvarMap }

        -- Phase 2: Partition acyclic / cyclic (body Expr IS the constraint)
        let (acyclic, _cyclic) ← (exprPartitionKVars body).run kctx

        -- Phase 3: Fusion — eliminate acyclic κ-vars via sol1 + elim1
        IO.println s!"[solve_fusion] Acyclic κ-vars: {acyclic.map (fun (k : KVar) => k.name)}"
        IO.println s!"[solve_fusion] Cyclic κ-vars:  {_cyclic.map (fun (k : KVar) => k.name)}"

        let mut solutions : List (KVar × Expr) := []
        let mut curr := body
        for κ in acyclic do
          IO.println s!"[solve_fusion] --- Eliminating κ = {κ.name} (params: {κ.params}) ---"

          let (sol, scopeNames) ← (computeSol κ curr (simplify := true)).run kctx
          IO.println s!"[solve_fusion]   scopeNames = {scopeNames}"

          let solFmt ← ppExpr sol
          IO.println s!"[solve_fusion]   sol1({κ.name}) = {solFmt}"

          solutions := solutions ++ [(κ, sol)]
          curr ← (exprElim1 κ curr).run kctx
          IO.println s!"[solve_fusion]   elim1 done, constraint updated"

        IO.println s!"[solve_fusion] --- All solutions ---"
        for (κ, sol) in solutions do
          let solFmt ← ppExpr sol
          IO.println s!"[solve_fusion]   {κ.name}({κ.params}) = {solFmt}"

        -- Build witness Exprs inside CPS (fvars alive for solToWitnessExpr)
        let mut witnessExprs : List Expr := []
        for κ in kvarsInOrder do
          let some (κSolved, sol) := solutions.find? (fun (k, _) => k.fvarId == κ.fvarId)
            | throwError "[solve_fusion] missing solution for κ {κ.name}"
          let witness ← solToWitnessExpr sol κSolved.params κSolved.paramTypes
          let witFmt ← ppExpr witness
          IO.println s!"[solve_fusion]   witness for {κSolved.name}: {witFmt}"
          witnessExprs := witnessExprs ++ [witness]
        return witnessExprs

      -- Phase 5: Apply witnesses directly as Exprs
      for witness in (witnesses : List Expr) do
        let goal ← getMainGoal
        let goalType ← goal.getType
        let goalType ← whnf goalType

        -- Debug: print goal type and witness type
        let goalFmt ← ppExpr goalType
        IO.println s!"[solve_fusion] Phase 5: goal type = {goalFmt}"

        let witTy ← inferType witness
        let witTyFmt ← ppExpr witTy
        IO.println s!"[solve_fusion] Phase 5: witness type = {witTyFmt}"

        -- Extract α and p from @Exists α p
        let α := goalType.getArg! 0
        let p := goalType.getArg! 1
        let αFmt ← ppExpr α
        let pFmt ← ppExpr p
        IO.println s!"[solve_fusion] Phase 5: α = {αFmt}"
        IO.println s!"[solve_fusion] Phase 5: p = {pFmt}"

        let αTy ← inferType α
        let αTyFmt ← ppExpr αTy
        IO.println s!"[solve_fusion] Phase 5: type of α = {αTyFmt}"

        -- Check: does witness typecheck against α?
        let isDefEq ← isDefEq witTy α
        IO.println s!"[solve_fusion] Phase 5: witTy =?= α: {isDefEq}"

        -- Try to build and apply
        try
          let obligation ← mkAppM' p #[witness]
          let oblFmt ← ppExpr obligation
          IO.println s!"[solve_fusion] Phase 5: obligation = {oblFmt}"
          let mvar ← mkFreshExprMVar (some obligation)
          let lvl := if α.isProp then levelZero else levelOne
          IO.println s!"[solve_fusion] Phase 5: using level = {lvl}"
          let proof := mkApp4 (mkConst ``Exists.intro [lvl]) α p witness mvar
          goal.assign proof
          replaceMainGoal [mvar.mvarId!]
          IO.println s!"[solve_fusion] Phase 5: assign OK"
        catch e =>
          IO.println s!"[solve_fusion] Phase 5: FAILED: {← e.toMessageData.toString}"
          throw e
    )
    (fun e => do
      logInfo m!"[solve_fusion] ✗ Solver failed: {e.toMessageData}"
      logInfo m!"[solve_fusion] → falling back to closeResidualGoals"
    )

  closeResidualGoals

syntax "solve_fusion" : tactic
elab_rules : tactic
  | `(tactic| solve_fusion) => solveFusionImpl
