import Lean
import Aesop

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad
import LeanFixpoint.Tactic.Utils

open Lean Elab Meta Tactic

initialize Lean.registerTraceClass `solveFusion

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
      let closers := #[
        `(tactic| omega),
        `(tactic| grind),
        `(tactic| aesop),
        `(tactic| (constructor <;> grind)),
        `(tactic| (simp_all; grind))
      ]
      let mut closed := false
      for c in closers do
        if !closed then
          let b ← attemptTactic (evalTactic (← c))
          if b then closed := true
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
    let _ ← attemptTactic (evalTactic (← `(tactic| simp only [])))
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
      let witnesses : List Expr ← peelExistentials reduced emptyKvars fun kvarMap body => do
        let kctx : KContext := { kvars := kvarMap }

        -- Phase 2: Expr → Constraint
        let constraint ← (exprToConstraint body).run kctx

        -- Phase 3: Partition acyclic / cyclic
        let (acyclic, _cyclic) ← (constraint.partitionKVars).run kctx

        -- Phase 4: Fusion — eliminate acyclic κ-vars via sol1 + elim1
        IO.println s!"[solve_fusion] Acyclic κ-vars: {acyclic.map (fun (k : KVar) => k.name)}"
        IO.println s!"[solve_fusion] Cyclic κ-vars:  {_cyclic.map (fun (k : KVar) => k.name)}"

        let mut solutions : List (Name × Expr × List Name) := []
        let mut curr := constraint
        for κ in acyclic do
          IO.println s!"[solve_fusion] --- Eliminating κ = {κ.name} (params: {κ.params}) ---"

          let scopedC ← (curr.scope κ).run kctx
          let scopeNames ← (collectScopeVars κ scopedC).run kctx
          let scopeFVars ← (collectScopeFVars κ scopedC).run kctx
          IO.println s!"[solve_fusion]   scopeNames = {scopeNames}"

          let sol ← do
            if scopeNames.length > 0 && κ.params.length > scopeNames.length then
              let stripped ← (stripScope κ scopedC).run kctx
              let s := stripped.sol1 κ (simplify := true)
              IO.println s!"[solve_fusion]   using STRIPPED sol1"
              -- Replace scope fvars with corresponding canonical params
              let numRefParams := κ.params.length - scopeFVars.length
              let scopeParamNames := κ.params.drop numRefParams
              let sFixed := (scopeFVars.zip scopeParamNames).foldl
                (fun acc (scopeFV, paramName) =>
                  acc.replaceFVar scopeFV (.fvar (FVarId.mk paramName))) s
              pure sFixed
            else
              let s := curr.sol1 κ (simplify := true)
              IO.println s!"[solve_fusion]   using FULL sol1"
              pure s

          let solFmt ← ppExpr sol
          IO.println s!"[solve_fusion]   sol1({κ.name}) = {solFmt}"

          solutions := solutions ++ [(κ.name, sol, κ.params)]
          curr ← (curr.elim1 κ).run kctx
          IO.println s!"[solve_fusion]   elim1 done, constraint updated"

        IO.println s!"[solve_fusion] --- All solutions ---"
        for (κName, sol, params) in solutions do
          let solFmt ← ppExpr sol
          IO.println s!"[solve_fusion]   {κName}({params}) = {solFmt}"

        -- Build witness Exprs (still inside CPS, fvars alive)
        let mut witnessExprs : List Expr := []
        for (κName, sol, params) in solutions do
          let witness ← solToWitnessExpr sol params
          let witFmt ← ppExpr witness
          IO.println s!"[solve_fusion]   witness for {κName}: {witFmt}"
          witnessExprs := witnessExprs ++ [witness]
        return witnessExprs

      -- Phase 5: Provide ∃ witnesses (in TacticM, fvars no longer needed —
      -- witnesses are closed Exprs thanks to Expr.abstract in sol1)
      for witness in (witnesses : List Expr) do
        let witnessSyn ← PrettyPrinter.delab witness
        evalTactic (← `(tactic| refine ⟨$witnessSyn, ?_⟩))
    )
    (fun e => do
      logInfo m!"[solve_fusion] ✗ Solver failed: {e.toMessageData}"
      logInfo m!"[solve_fusion] → falling back to closeResidualGoals"
    )

  closeResidualGoals

syntax "solve_fusion" : tactic
elab_rules : tactic
  | `(tactic| solve_fusion) => solveFusionImpl
