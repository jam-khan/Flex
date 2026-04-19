import Lean
import Aesop

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad
import LeanFixpoint.Tactic.Utils
import LeanFixpoint.Tactic.Tactics
import LeanFixpoint.Solve.Fixpoint

open Lean Elab Meta Tactic

initialize Lean.registerTraceClass `solveFixpoint

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
    let _ ← attemptTactic (evalTactic (← `(tactic| dsimp only)))
    let _ ← attemptTactic (evalTactic (← `(tactic| zap)))
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

      let emptyKvars : Std.HashMap FVarId KVar := {}
      let witnesses : List Expr ← peelExistentials reduced emptyKvars fun kvarMap body => do
        let kctx : KContext := { kvars := kvarMap }

        -- Phase 2: Partition
        let (acyclic, cyclic) ← (exprPartitionKVars body).run kctx
        IO.println s!"[solve_fixpoint] Acyclic κ-vars: {acyclic.map (·.name)}"
        IO.println s!"[solve_fixpoint] Cyclic κ-vars:  {cyclic.map (·.name)}"

        -- Phase 3: Fusion for acyclic
        let mut solutions : List (Name × Expr × List Name × List Expr) := []
        let mut curr := body
        for κ in acyclic do
          IO.println s!"[solve_fixpoint] --- Fusion: {κ.name} (params: {κ.params}) ---"
          let (sol, _) ← (computeSol κ curr (simplify := true)).run kctx
          let solFmt ← ppExpr sol
          IO.println s!"[solve_fixpoint]   sol1({κ.name}) = {solFmt}"
          solutions := solutions ++ [(κ.name, sol, κ.params, κ.paramTypes)]
          curr ← (exprElim1 κ curr).run kctx

        -- Phase 4: Predicate abstraction for cyclic (NEW vs solve_fusion)
        if !cyclic.isEmpty then
          IO.println s!"[solve_fixpoint] --- PA on cyclic κ's ---"
          let flatCs ← (exprFlat curr).run kctx
          IO.println s!"[solve_fixpoint]   {flatCs.length} flat clauses"
          let paSols ← predicateAbstraction kctx cyclic flatCs
          for (κ, sol) in paSols do
            let solFmt ← ppExpr sol
            IO.println s!"[solve_fixpoint]   PA sol for {κ.name}: {solFmt}"
            solutions := solutions ++ [(κ.name, sol, κ.params, κ.paramTypes)]

        IO.println s!"[solve_fixpoint] --- All solutions ---"
        for (κName, sol, params, _) in solutions do
          let solFmt ← ppExpr sol
          IO.println s!"[solve_fixpoint]   {κName}({params}) = {solFmt}"

        -- Build witness Exprs
        let mut witnessExprs : List Expr := []
        for (κName, sol, params, paramTypes) in solutions do
          let witness ← solToWitnessExpr sol params paramTypes
          let witFmt ← ppExpr witness
          IO.println s!"[solve_fixpoint]   witness for {κName}: {witFmt}"
          witnessExprs := witnessExprs ++ [witness]
        return witnessExprs

      -- Phase 5: Apply witnesses
      for witness in (witnesses : List Expr) do
        let goal ← getMainGoal
        let goalType ← goal.getType
        let goalType ← whnf goalType
        let α := goalType.getArg! 0
        let p := goalType.getArg! 1
        let obligation ← mkAppM' p #[witness]
        let mvar ← mkFreshExprMVar (some obligation)
        let lvl := if α.isProp then levelZero else levelOne
        let proof := mkApp4 (mkConst ``Exists.intro [lvl]) α p witness mvar
        goal.assign proof
        replaceMainGoal [mvar.mvarId!]
    )
    (fun e => do
      logInfo m!"[solve_fixpoint] ✗ Solver failed: {e.toMessageData}"
      logInfo m!"[solve_fixpoint] → falling back to closeResidualGoals"
    )

  closeResidualGoals

syntax "solve_fixpoint" : tactic
elab_rules : tactic
  | `(tactic| solve_fixpoint) => solveFixpointImpl
