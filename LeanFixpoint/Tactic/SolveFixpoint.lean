import Lean
import Aesop

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad
import LeanFixpoint.Tactic.Internal.Utils
import LeanFixpoint.Tactic.Zap
import LeanFixpoint.Tactic.Internal.CloseLoop
import LeanFixpoint.Tactic.SplitHyps
import LeanFixpoint.Solve.Fixpoint

open Lean Elab Meta Tactic

initialize Lean.registerTraceClass `solveFixpoint

private def closeResidualGoals : TacticM Unit := do
  let goals ← getGoals
  if goals.isEmpty then pure ()
  else
    let _ ← attemptTactic (evalTactic (← `(tactic| dsimp only)))
    let _ ← attemptTactic (evalTactic (← `(tactic| zap)))
    let goals ← getGoals
    if goals.isEmpty then pure ()
    else
      -- Try elimT before the heavier simp_all/grind fixpoint or closeLoop.
      -- elimT (= trivialk; simp; zap) is bounded and handles the typical
      -- post-fusion shape: trivial witnesses for leftover ∃-κ binders,
      -- one simp pass, then ∀/∧ decomposition with grind at leaves.
      let _ ← attemptTactic (evalTactic (← `(tactic| elimT)))
      let goals ← getGoals
      if goals.isEmpty then pure ()
      else
        let _ ← attemptTactic (evalTactic (←
          `(tactic| all_goals (split_hyps; all_goals simp_all; all_goals grind))))
        let goals ← getGoals
        if goals.isEmpty then pure ()
        else closeLoop


/-!
  ## `solve_fixpoint` tactic

  Fusion for acyclic κ's (copy of `solve_fusion`) PLUS predicate abstraction
  for cyclic κ's, drawing qualifiers from `@[qualif]`-tagged decls.

  Expected to handle every example in `Demo/Cyclic.lean` and benchmarks with
  invariants expressible as a conjunction of tagged qualifier instantiations.
-/
private def solveFixpointImpl : TacticM Unit := withMainContext do
  -- Unfolding essentially
  let goal ← getMainGoal
  let _    ← attemptTactic
    (do let newGoal ← goal.withContext do
          let target   ← goal.getType
          let unfolded ← unfoldDefinition target
          goal.replaceTargetDefEq unfolded
        replaceMainGoal [newGoal])
  -- Peel ∃ κ : T, .. into κ-MVars via Exists.intro
  --    After this, the κ-mvars are part of the proof scaffolding and
  --    `bodyGoal` is the residual proof obligation with κs replaced
  --    by their mvars.
  let goal ← getMainGoal
  let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
  replaceMainGoal [bodyGoal]

  let kctx : KContext := { kvars := kvarMap }

  let _ ← tryCatch
    (do
      let bodyGoal ← getMainGoal
      let body     ← bodyGoal.getType
      let body     ← reduce body

      -- Partition acyclic vs cyclic κ-vars
      let (acyclic, cyclic) ← (exprPartitionKVars body).run kctx
      IO.println s!"[solve_fixpoint] Acyclic κ: {acyclic.map (·.name)}"
      IO.println s!"[solve_fixpoint] Cyclic κ:  {cyclic.map (·.name)}"

      -- Fusion for acyclic κs. Each sol becomes a closed lambda and
      -- is assigned to its κ-mvar immediately. No cleanliness filter:
      -- sols may reference other κ-mvars; instantiateMVars resolves them.
      let mut curr := body
      for κ in acyclic do
        IO.println s!"[solve] --- {κ.name} ---"
        let (sol, _) ← (computeSol κ curr).run kctx
        IO.println s!"[solve]   sol = {← ppExpr sol}"
        let lam ← solToWitnessExpr sol κ.params κ.paramTypes
        IO.println s!"[solve]   lam = {← ppExpr lam}"

        -- Occurs check: skip if lam references κ itself.
        let selfRef := lam.find? fun sub =>
          sub.isMVar && sub.mvarId! == κ.mvarId
        if selfRef.isSome then
          IO.println s!"[solve]   ⚠ {κ.name}: sol self-references — leaving as user goal"
          -- don't assign, don't exprElim1; loop continues with curr unchanged
        else
          κ.mvarId.assign lam
          curr ← (exprElim1 κ curr).run kctx

      -- Predicate abstraction for cyclic κs.
      if !cyclic.isEmpty then
        IO.println s!"[solve_fixpoint] --- PA on cyclic κ's ---"
        let flatCs ← (exprFlat curr).run kctx
        let paSols ← predicateAbstraction kctx cyclic flatCs
        for (κ, sol) in paSols do
          IO.println s!"[solve_fixpoint]   PA sol for {κ.name} = {← ppExpr sol}"
          let lam ← solToWitnessExpr sol κ.params κ.paramTypes
          κ.mvarId.assign lam
    )
    (fun e => do
      logInfo m!"[solve_fixpoint] ✗ Solver failed: {e.toMessageData}"
      logInfo m!"[solve_fixpoint] → leaving unfilled κs as user goals")

  -- 4. Expose unfilled κ-mvars as user goals so the user can `exact`
  --    a witness when fusion or PA didn't fully solve them.
  let unfilled ← kvarsInOrder.filterMapM fun κ => do
    if (← κ.mvarId.isAssigned) then return none
    else return some κ.mvarId

  if unfilled.isEmpty then
    closeResidualGoals
  else
    let residual ← getMainGoal
    -- κs first so the user fills them before tackling the residual,
    -- which depends on them.
    setGoals (unfilled ++ [residual])
    logInfo m!"[solve_fixpoint] {unfilled.length} κ(s) left as user goal(s) — \
                 fill each with `exact (fun z0 z1 ... => ...)`."

syntax "solve_fixpoint" : tactic
elab_rules : tactic
  | `(tactic| solve_fixpoint) => solveFixpointImpl
