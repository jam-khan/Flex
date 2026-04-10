import Lean

import Aesop
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Solve.Fixpoint
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Tactic.Utils

open Lean Elab Meta Command Tactic

-- Register a trace class (toggle with `set_option trace.solveFixpoint true`)
initialize Lean.registerTraceClass `solveFixpoint

private def tryClosers : TacticM Bool := do
  let b ← attemptTactic (evalTactic (← `(tactic| native_decide)))
  match b with
  | Bool.true => logInfo m!"[solve_fixpoint] closed by: native_decide"; pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| grind)))
  match b with
  | Bool.true => logInfo m!"[solve_fixpoint] closed by: grind"; pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| aesop)))
  match b with
  | Bool.true => logInfo m!"[solve_fixpoint] closed by: aesop"; pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| omega)))
  match b with
  | Bool.true => logInfo m!"[solve_fixpoint] closed by: omega"; pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| (constructor <;> grind))))
  match b with
  | Bool.true => logInfo m!"[solve_fixpoint] closed by: constructor+grind"; pure Bool.true
  | Bool.false =>
  let b ← attemptTactic (evalTactic (← `(tactic| (simp_all; grind))))
  match b with
  | Bool.true => logInfo m!"[solve_fixpoint] closed by: simp_all+grind"; pure Bool.true
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
        -- Try unfolding if required
        let didUnfold ← attemptTactic do
          let newGoal ← g.withContext do
            let target ← g.getType
            let u ← unfoldDefinition target
            g.replaceTargetDefEq u
          replaceMainGoal (newGoal :: restGoals)
        if didUnfold then
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

-- Format qualifiers for printing
private def formatQualifier (q : Qualifier) : String :=
  let ps := String.intercalate ", " (q.params.map fun p => s!"{p.sym} : {toString p.sort}")
  s!"{q.name}({ps}) | {toString q.body}"

private def elaborateQualifiers (qs? : Option (TSyntax `term)) : TacticM (Option (List Qualifier)) :=
  -- logging the qualifiers first
  match qs? with
  -- no qualifiers passed
  | none       => do
    logInfo m!"[solve_fixpoint] Qualifiers: no argument passed"
    return none
  -- term passed for qualifiers
  | some qsSyn =>
      tryCatch
        (do
          -- elaborate the qualifier syntax into a term with expected type
          -- of a list of qualifiers
          let qsExpr ← elabTerm qsSyn
            (some (mkApp (mkConst ``List [.zero]) (mkConst ``Qualifier)))
          -- resolve `?m` meta-variables inside
          let qsExpr  ← instantiateMVars qsExpr
          -- finally, evaluate the expression and give an evaluated lean value
          -- takes the type `List Qualifier` which is top-level `Lean` type
          -- also, take `Expr` of the same type
          -- and the expression to evaluate, here `qsExpr`
          let quals   ← unsafe Lean.Meta.evalExpr (List Qualifier)
                        (mkApp (mkConst ``List [.zero]) (mkConst ``Qualifier)) qsExpr

          if quals.isEmpty then
            logInfo m!"[solve_fixpoint] Qualifiers: empty list provided"
          else
            let lines := String.intercalate "\n" (quals.map fun q => s!" · {formatQualifier q}")
            logInfo m!"[solve_fixpoint] Qualifiers ({quals.length}):\n{lines}"
          return quals
        )
        (fun _ => do
          logInfo m!"[solve_fixpoint] Qualifiers: argument could not be reflected as List Qualifier"
          return none
        )

private def solveFixpointImpl (qs? : Option (TSyntax `term)) : TacticM Unit := withMainContext do

  -- elaborate and log qualifiers
  let quals? ← elaborateQualifiers qs?
  let _ ← attemptTactic (evalTactic (← `(tactic| intros)))

  let goal ← getMainGoal
  let _ ← attemptTactic
    (do let newGoal ← goal.withContext do
          let target   ← goal.getType
          let unfolded ← unfoldDefinition target
          goal.replaceTargetDefEq unfolded
        replaceMainGoal [newGoal])

  let goal ← getMainGoal
  let solverResult ← tryCatch
    (do
      let fvarsRef ← IO.mkRef ({} : FVarMap)
      let kvarsRef ← IO.mkRef ({} : KVarSet)

      -- Below we add any local context variables in the fvars
      let lctx ← getLCtx
      for decl in lctx do
        if !decl.isAuxDecl then
          fvarsRef.modify fun m => m.insert decl.fvarId decl.userName

      let goalType ← goal.getType
      let reduced  ← reduce goalType
      let propAST  ← toPropASTWithTracking fvarsRef kvarsRef reduced
      let fvarMap  ← fvarsRef.get
      let kvarSet  ← kvarsRef.get
      let constraint ← toConstraint fvarMap kvarSet propAST
      -- let kvars := constraint.kvars.eraseDups

      -- Phase 1: Partition into acyclic / cyclic
      let (acyclic, cyclic) := constraint.partitionKVars
      logInfo m!"[solve_fixpoint] Acyclic: {acyclic.map (·.name)}"
      logInfo m!"[solve_fixpoint] Cyclic:  {cyclic.map (·.name)}"

      -- Phase 2: Fusion - eliminate acyclic κ-vars
      -- solutions need name of κ, solution pred and list of κ formal params
      let mut solutions : List (Name × Pred × List Name) := []
      let mut curr := constraint
      for κ in acyclic do
        -- Use stripped solution only when kappa type includes scope variables
        -- (i.e., kappa has more params than scope vars, so there are dedicated scope positions)
        let scopedC := curr.scope κ
        let scopeNames : List Name := collectScopeVars κ scopedC
        let sol :=
          if scopeNames.length > 0 && κ.params.length > scopeNames.length then
            -- Stripped sol1: scope vars become free, then substitute with canonical params
            let stripped := stripScope κ scopedC
            let sol := stripped.sol1 κ
            let numRefParams := κ.params.length - scopeNames.length
            let scopeParams := κ.params.drop numRefParams
            ((scopeNames.zip scopeParams).foldl
              (fun acc (origName, canonName) => acc.substVar origName canonName) sol).simplify
          else
            -- Kappa type doesn't include scope vars — use full sol1
            curr.sol1 κ
        solutions := solutions ++ [(κ.name, sol, κ.params)]
        curr := curr.elim1 κ

      for (κName, sol) in solutions do
        logInfo m!"[solve_fixpoint] Solution: {κName} := {toString sol}"

      -- Phase 3: Predicate abstraction - handle cyclic κ-vars
      if !cyclic.isEmpty then
        match quals? with
        | some Q => do
          let pa ← predicateAbstraction curr Q
          for (κ, qs) in pa do
            let sol   := conjoinQualifiers qs
            solutions := solutions ++ [(κ.name, sol, κ.params)]
            curr      := curr.elimStar κ sol
        | none   => logWarning m!"[solve_fixpoint] Cyclic κ-vars present but no qualifiers provided"

      -- NOTE: One may need to be careful with order of instantiations
      -- Phase 4: Witness synthesis for acyclic solutions
      for (_κName, sol, params) in solutions do
        logInfo m!"[solve_fixpoint] Elaborating witness for: {toString sol}"
        let mut env₀ : VarMap := {}
        let lctx ← getLCtx
        for decl in lctx do
          if !decl.isAuxDecl then
            env₀ := env₀.insert decl.userName (mkFVar decl.fvarId)
        let witness ← solToWitnessExpr sol params env₀
        let witnessSyn ← PrettyPrinter.delab witness
        evalTactic (← `(tactic| refine ⟨$witnessSyn, ?_⟩))
    )
    (fun e => do
      logInfo m!"[solve_fixpoint] ✗ Solver failed: {e.toMessageData}"
      logInfo m!"[solve_fixpoint] → falling back to closeResidualGoals"
      )

  let _ := solverResult
  let _ := qs?

  closeResidualGoals

-- declare syntax for solve_fixpoint
syntax "solve_fixpoint" : tactic
syntax "solve_fixpoint" "with" term : tactic

elab_rules : tactic
  | `(tactic| solve_fixpoint)           => solveFixpointImpl none
  | `(tactic| solve_fixpoint with $qs)  => solveFixpointImpl (some qs)

syntax "solve_residual" : tactic
elab_rules : tactic
  | `(tactic | solve_residual) => do
    closeResidualGoals
