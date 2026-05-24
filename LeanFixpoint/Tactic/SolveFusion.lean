import Lean

import LeanFixpoint.Fusion.Types
import LeanFixpoint.Fusion.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad
import LeanFixpoint.Tactic.Internal.Utils
import LeanFixpoint.Tactic.Zap
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
      -- Phase 2: split all ∨/∧/∃ in hypotheses, then grind.
      -- `simp_all` removed: its `maxRecDepth` is logged via diagnostics,
      -- not thrown, so `attemptTactic` can't swallow it.
      let _ ← attemptTactic (evalTactic (←
        `(tactic| all_goals (split_hyps; all_goals grind))))
      let goals ← getGoals
      if goals.isEmpty then pure ()
      else closeLoop

/-!
  ## `solve_fusion` tactic (mvar-based)

  Handles acyclic κ-vars via fusion (sol1 + elim1). No predicate abstraction.
  Cyclic κ-vars are left unassigned and exposed as user goals so the user
  can supply a witness manually (`exact (fun z0 z1 ... => ...)`).

  Flow:
    1. Unfold def at the head so ∃s are visible.
    2. `peelExistentialsAndIntro` discharges each ∃ with a fresh
       syntheticOpaque κ-mvar; the residual proof goal becomes main.
    3. Partition κs into acyclic / cyclic.
    4. Fusion: for each acyclic κ, compute sol → closed lambda → assign.
       Sols may freely reference other κ-mvars; instantiateMVars resolves
       the chain when the proof is finalised.
    5. Any unassigned κ (all cyclic ones, plus any acyclic that errored)
       is exposed as a user goal.
    6. If everything is assigned, `closeResidualGoals` discharges the
       residual proof obligation.
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

  -- 2. Peel ∃ into κ-mvars via Exists.intro
  let goal ← getMainGoal
  let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
  replaceMainGoal [bodyGoal]

  let kctx : KContext := { kvars := kvarMap }

  let _ ← tryCatch
    (do
      let bodyGoal ← getMainGoal
      let body     ← bodyGoal.getType
      let body     ← reduce body

      let (acyclic, cyclic) ← (exprPartitionKVars body).run kctx
      IO.println s!"[solve_fusion] Acyclic κ: {acyclic.map (·.name)}"
      IO.println s!"[solve_fusion] Cyclic κ: {cyclic.map (·.name)} (left to user)"

      -- Fusion for acyclic κs.
      let mut curr := body
      for κ in acyclic do
        IO.println s!"[solve_fusion] --- Fusion: {κ.name} ---"
        let (sol, curr') ← (exprElim1 κ curr).run kctx
        IO.println s!"[solve_fusion]  sol1({κ.name}) = {← ppExpr sol}"
        let lam ← solToWitnessExpr sol κ.params κ.paramTypes
        IO.println s!"[solve_fusion]  assign {κ.name} := {← ppExpr lam}"
        κ.mvarId.assign lam
        curr := curr'

    )
    (fun e => do
      logInfo m!"[solve_fusion] ✗ Fusion failed: {e.toMessageData}"
      logInfo m!"[solve_fusion] → leaving any unfilled κs as user goals")

  -- 4. Expose unfilled κ-mvars as user goals. This includes:
  --    · all cyclic κs (fusion can't solve them on its own)
  --    · any acyclic κ that fusion errored on before assignment
  let unfilled ← kvarsInOrder.filterMapM fun κ => do
    if (← κ.mvarId.isAssigned) then return none
    else return some κ.mvarId

  if unfilled.isEmpty then
    closeResidualGoals
  else
    let residual ← getMainGoal
    -- κs first so the user fills them before tackling the residual.
    setGoals (unfilled ++ [residual])
    logInfo m!"[solve_fusion] {unfilled.length} κ(s) left as user goal(s) — \
                 fill each with `exact (fun z0 z1 ... => ...)`."

syntax "solve_fusion" : tactic
elab_rules : tactic
  | `(tactic| solve_fusion) => solveFusionImpl
