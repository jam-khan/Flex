import LeanFixpoint.Tactic.Tactics.RewriteKs
import LeanFixpoint.Core
import LeanFixpoint.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Zap

open Lean Meta Elab Tactic

syntax "fusion" : tactic

partial def destructAndBuild
    (kvars : Array KVar)
    (kLams : List (KVar × Expr))
    (bodyWithMvars : Expr)
    (originalType : Expr)
    (residualOut : IO.Ref (Array MVarId))
    (curWit : Expr) (curWitTy : Expr)
    (cycRem : List KVar)
    (cycAcc : Array (KVar × Expr)) :
    MetaM Expr := do
  match cycRem with
  | [] =>
    -- curWit : c′_with_cyclic_fvars. Use it as h_c' for walkPhase5.
    let bodyFV := replaceKMvarsWithFvars
      (cycAcc.toList.map fun (κ, fv) => (κ.mvarId, fv))
      bodyWithMvars
    let bodyProof ← walkPhase5 kLams bodyFV curWit [] [] [] residualOut
    -- Build Exists.intro chain in ORIGINAL κ-order over originalType.
    let kLamMap : Std.HashMap MVarId Expr :=
      kLams.foldl (fun m (κ, lam) => m.insert κ.mvarId lam)
        (∅ : Std.HashMap MVarId Expr)
    let cycFvMap : Std.HashMap MVarId Expr :=
      cycAcc.foldl (fun m (κ, fv) => m.insert κ.mvarId fv)
        (∅ : Std.HashMap MVarId Expr)
    let rec buildIntros (curType : Expr) (idx : Nat) : MetaM Expr := do
      let curType ← whnf curType
      if curType.isAppOfArity ``Exists 2 then
        let α := curType.appFn!.appArg!
        let pred := curType.appArg!
        let κmvar := kvars[idx]!.mvarId
        let witness ← match kLamMap.get? κmvar with
          | some lam => pure lam
          | none =>
            match cycFvMap.get? κmvar with
            | some fv => pure fv
            | none => throwError "zapAcyclic: no witness for κ idx={idx}"
        let restType := pred.beta #[witness]
        let restProof ← buildIntros restType (idx + 1)
        mkAppOptM ``Exists.intro
          #[some α, some pred, some witness, some restProof]
      else
        return bodyProof
    buildIntros originalType 0
  | κ :: rest => do
    let curWitTyW ← whnf curWitTy
    let α    := curWitTyW.appFn!.appArg!
    let pred := curWitTyW.appArg!
    withLocalDeclD κ.name α fun κfv => do
      let nextTy := pred.beta #[κfv]
      withLocalDeclD `h_inner nextTy fun innerFv => do
        let innerProof ← destructAndBuild kvars kLams bodyWithMvars
          originalType residualOut innerFv nextTy rest
          (cycAcc.push (κ, κfv))
        let elimLam ← mkLambdaFVars #[κfv, innerFv] innerProof
        mkAppOptM ``Exists.elim
          #[some α, some pred, none, some curWit, some elimLam]

elab_rules : tactic
  | `(tactic| fusion) => withMainContext do
      let goal ← getMainGoal
      let originalType ← goal.getType

      -- Stash data computed inside the withPeeledExists closure.
      let dataRef : IO.Ref (Option (
          Expr                              -- newGoalType
        × List (KVar × Expr)                -- kLams (acyclic only)
        × List KVar                         -- acyclic κs
        × List KVar                         -- cyclic κs
        × Array KVar                        -- kvars in original ∃-order
        × Expr                              -- bodyWithMvars
        )) ← IO.mkRef none

      withPeeledExists originalType #[] fun binders body => do
        if binders.size == 0 then
          throwError "zapAcyclic: goal has no ∃-binders"

        -- Build fresh κ-mvars + substitute fvar → mvar in body for KM classification.
        let mut kvars : Array KVar := #[]
        let mut bodyWithMvars := body
        for (name, ty, fvar) in binders do
          let paramTypes ← collectArrowTypes ty
          let params := (List.range paramTypes.length).map fun i =>
            Name.mkSimple s!"z{i}"
          let mvar ← mkFreshExprMVar (some ty) (kind := .syntheticOpaque)
          kvars := kvars.push
            { name, params, paramTypes, mvarId := mvar.mvarId! }
          bodyWithMvars := bodyWithMvars.replaceFVar fvar mvar

        let kctxMap := kvars.foldl
          (fun acc k => acc.insert k.mvarId k) (∅ : Std.HashMap MVarId KVar)
        let kctx : KContext := { kvars := kctxMap }
        let (acyclic, cyclic) ← (exprPartitionKVars bodyWithMvars).run kctx

        if acyclic.isEmpty then
          dataRef.set none
          return

        -- Acyclic loop: compute kLams + curr.
        let mut curr := bodyWithMvars
        let mut kLams : List (KVar × Expr) := []
        for κ in acyclic do
          let scoped' ← (exprScopePres κ curr).run kctx
          let sol    ← (exprSol1Pres κ scoped').run kctx
          let sol    := simplifyAndExists sol
          let lam    ← solToWitnessExpr sol κ.params κ.paramTypes
          kLams := kLams ++ [(κ, lam)]
          curr   ← (exprElimStar κ sol curr).run kctx

        -- Assign acyclic κ-mvars to their lambdas so Lean's defeq treats
        -- κ-mvar applications in bodyFV as β-reduced σ̂. Required for the
        -- bridge proof to typecheck against `Exists.intro pred witness` shapes.
        for (κ, lam) in kLams do κ.mvarId.assign lam

        -- Substitute cyclic-κ-mvars in curr with original fvars (still in scope).
        let cyclicSubst : List (MVarId × Expr) := cyclic.map fun κ =>
          let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
          (κ.mvarId, binders[idx]!.2.2)
        let curr_fv := replaceKMvarsWithFvars cyclicSubst curr

        -- Build new goal type by abstracting cyclic fvars into an ∃-chain.
        let cyclicBinders : Array (Name × Expr × Expr) :=
          cyclic.toArray.map fun κ =>
            let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
            binders[idx]!
        let newGoalType ← mkExistsChain cyclicBinders curr_fv

        dataRef.set (some (newGoalType, kLams, acyclic, cyclic, kvars,
                           bodyWithMvars))

      -- ─── Back in original lctx ─────────────────────────────────────────
      let some (newGoalType, kLams, acyclic, cyclic, kvars, bodyWithMvars)
        ← dataRef.get
        | do
            logInfo m!"zapAcyclic: no acyclic κs to eliminate"
            return

      -- Create bridge and new-goal mvars in original lctx.
      let bridgeType ← goal.withContext do
        mkArrow newGoalType originalType
      let bridgeMvar ← mkFreshExprMVar (some bridgeType) (kind := .syntheticOpaque)
      let newGoalM  ← mkFreshExprMVar (some newGoalType) (kind := .syntheticOpaque)
      goal.assign (mkApp bridgeMvar newGoalM)

      -- ─── Construct bridge term: λ h => Exists.elim … walkPhase5 ──────
      let residualOut ← IO.mkRef #[]

      let bridge ← withLocalDeclD `h newGoalType fun h_fv => do
        let inner ← destructAndBuild kvars kLams bodyWithMvars originalType
          residualOut h_fv newGoalType cyclic #[]
        mkLambdaFVars #[h_fv] inner

      bridgeMvar.mvarId!.assign bridge

      let residuals := (← residualOut.get).toList
      logInfo m!"zapAcyclic: eliminated {acyclic.length} acyclic κ \
                {acyclic.map (·.name)}; new goal is ∃ \
                {cyclic.length} cyclic κ + body; \
                {residuals.length} residual obligation(s)"
      replaceMainGoal (newGoalM.mvarId! :: residuals)

-- ───────────────────────────────────────────────────────────────────────
-- Tests for zapAcyclic
-- ───────────────────────────────────────────────────────────────────────

/-- A-test: one acyclic κ. zapAcyclic should leave only the non-κ leaf. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion
  all_goals first | rfl | grind

/-- B-test: two independent acyclic κs.  zapAcyclic should leave two
    non-κ leaves. -/
example :
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  fusion
  all_goals first | rfl | grind

/-- D-test (Phase 5): mixed — κ1 cyclic (self-loop), κ2 acyclic.
    zapAcyclic eliminates κ2 in-place; residual is the single ∃-form goal
    `∃ κ1, c′`. The cyclic-κ1 witness `λ y => 0 ≤ y` is supplied manually
    (grind cannot synthesize it). -/
example : ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
      (∀ y : Int, κ1 y → κ1 (y + 1))
    ∧ (∀ ν : Int, ν = 0 → κ1 ν)
    ∧ (∀ ν : Int, ν = 0 → κ2 ν)
    ∧ (∀ z : Int, κ2 z → 0 ≤ z) := by
  fusion
  exact ⟨fun y => 0 ≤ y, by grind⟩
