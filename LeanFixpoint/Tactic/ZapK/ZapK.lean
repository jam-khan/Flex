import LeanFixpoint.Tactic.RewriteKs
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr

open Lean Meta Elab Tactic

-- ───────────────────────────────────────────────────────────────────────
-- simplifyAndExists — collapse `_ ∧ False / False ∧ _ → False`,
-- `∃ x, False → False`, `True ∧ X → X`, but DO NOT touch Or-trees.
-- Used to drop dead κ-references from sol expressions (e.g. a sol_κx
-- branch like `(κy y x n p) ∧ (∃ ν, ν=y+1 ∧ False)` collapses to False
-- without breaking the goal's And-tree ↔ sol's Or-tree position mirror.
-- ───────────────────────────────────────────────────────────────────────
private partial def simplifyAndExists (e : Expr) : Expr :=
  if e.isAppOfArity ``And 2 then
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    if l.isConstOf ``False || r.isConstOf ``False then mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  else if e.isAppOfArity ``Or 2 then
    -- Recurse into Or branches but keep the Or-node — path-mirror requires
    -- positional preservation. Branches may collapse to False internally;
    -- that's the desired "dead branch" shape.
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    mkApp2 (mkConst ``Or) l r
  else if e.isAppOfArity ``Exists 2 then
    let ty := e.appFn!.appArg!
    let body := e.appArg!
    let univrs := e.getAppFn.constLevels!
    match body with
    | .lam n t b bi =>
      let b' := simplifyAndExists b
      if b'.isConstOf ``False then mkConst ``False
      else mkApp2 (mkConst ``Exists univrs) ty (.lam n t b' bi)
    | _ => e
  else if e.isForall then
    match e with
    | .forallE n t b bi =>
      let t' := simplifyAndExists t
      let b' := simplifyAndExists b
      .forallE n t' b' bi
    | _ => e
  else e

/-! # zapK — fused proof-term emitter

  Single recursive walk over the body goal. At ∀/∧ nodes builds the outer
  proof (λ-abstraction / `And.intro`) inline, accumulating an `orPath` of
  `inL/inR` choices through ∧-splits and binders/guards through ∀-intros.
  At κᵢ-headed leaves, β-reduces `lam_κᵢ args` (computed via the existing
  `exprSol1` + `solToWitnessExpr` Phase 1) and navigates the resulting
  ∃-∧-∨ structure using orPath/binders/guards in lockstep. Eq leaves
  become residual mvars (auto-rfl handling lives in a later iteration).
-/

-- ───────────────────────────────────────────────────────────────────────
-- Expr-construction primitives
-- ───────────────────────────────────────────────────────────────────────

private def mkExistsIntro (α predLam w proof : Expr) : MetaM Expr := do
  let u ← getLevel α
  return mkApp4 (mkConst ``Exists.intro [u]) α predLam w proof

private def mkAndIntro (a b ha hb : Expr) : Expr :=
  mkApp4 (mkConst ``And.intro) a b ha hb

private def mkOrInl (a b h : Expr) : Expr := mkApp3 (mkConst ``Or.inl) a b h
private def mkOrInr (a b h : Expr) : Expr := mkApp3 (mkConst ``Or.inr) a b h

private def mkEqRefl (ty x : Expr) : MetaM Expr := do
  let u ← getLevel ty
  return mkApp2 (mkConst ``Eq.refl [u]) ty x

-- ───────────────────────────────────────────────────────────────────────
-- Preserve-And scope/sol1 for ZapK
--
-- `exprScope` / `exprSol1` in `Core/Fusion.lean` strip non-κ branches
-- of `∧` — that form is what `solve_fixpoint` is tuned for. ZapK needs
-- the FULL And-tree preserved so the goal's And ↔ sol's Or position
-- mirror holds (otherwise walkProof's orPath bits land on the wrong
-- Or branch). These local copies do exactly that.
-- ───────────────────────────────────────────────────────────────────────

private partial def exprScopePres (κ : KVar) (e : Expr) : KM Expr := do
  if e.and?.isSome then
    return e
  else if e.isForall then
    let dom := e.bindingDomain!
    if !(← KM.exprKVars dom).contains κ then
      withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
        let sc ← exprScopePres κ (e.bindingBody!.instantiate1 fvar)
        let abstr := sc.abstract #[fvar]
        pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
    else
      return mkConst ``False
  else
    return e

private partial def exprSol1Pres (κ : KVar) (e : Expr) : KM Expr := do
  let e ← exprScopePres κ e
  if let some (l, r) := e.and? then
    return mkApp2 (mkConst ``Or) (← exprSol1Pres κ l) (← exprSol1Pres κ r)
  else if e.isForall then
    let name := e.bindingName!
    let dom := e.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp then
      return ← withLocalDeclD name dom fun pfvar => do
        let body ← whnf (e.bindingBody!.instantiate1 pfvar)
        let inner ← exprSol1Pres κ body
        return mkApp2 (mkConst ``And) dom inner
    else
      return ← withLocalDeclD name dom fun fvar => do
        let body ← whnf (e.bindingBody!.instantiate1 fvar)
        let conjunct ← do
          if body.isForall then
            let p := body.bindingDomain!
            let pSort ← (inferType p >>= whnf : MetaM Expr)
            if pSort.isProp then
              withLocalDeclD body.bindingName! p fun pfvar => do
                let c'  := body.bindingBody!.instantiate1 pfvar
                let inner ← exprSol1Pres κ c'
                return mkApp2 (mkConst ``And) p inner
            else
              exprSol1Pres κ body
          else
            exprSol1Pres κ body
        let abstr := conjunct.abstract #[fvar]
        let lam   := Expr.lam name dom abstr .default
        return mkApp2 (mkConst ``Exists [levelOne]) dom lam
  else if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
    let args := e.getAppArgs.toList
    let eqs := (κ.params.zip (args.zip κ.paramTypes)).map fun (pi, (ai, ty)) =>
      mkApp3 (mkConst ``Eq [levelOne]) ty (.fvar (FVarId.mk pi)) ai
    match eqs with
    | []      => return mkConst ``True
    | [eq]    => return eq
    | eq :: rest => return rest.foldl (mkApp2 (mkConst ``And)) eq
  else
    return mkConst ``False

-- ───────────────────────────────────────────────────────────────────────
-- κ-head detection
-- ───────────────────────────────────────────────────────────────────────

private def kHead? (kLams : List (KVar × Expr)) (goal : Expr) :
    Option (KVar × Expr × Array Expr) :=
  let fn := goal.getAppFn
  if fn.isMVar then
    kLams.find? (fun (κ, _) => κ.mvarId == fn.mvarId!) |>.map
      fun (κ, lam) => (κ, lam, goal.getAppArgs)
  else
    none

-- ───────────────────────────────────────────────────────────────────────
-- Eq-leaf proof construction
-- ───────────────────────────────────────────────────────────────────────

/-- Build a proof of an Eq / And-of-Eqs / True / False expression.
    Eq leaves auto-discharge via `isDefEq` when LHS/RHS are syntactically
    equal up to defeq (the common case: every eq comes from `zᵢ = aᵢ` where
    both sides reduce to the same value-binder fvar). Non-rfl eqs and
    `False` leaves become residual mvars. -/
private partial def buildEqProof (e : Expr) (residualOut : IO.Ref (Array MVarId)) :
    MetaM Expr := do
  if e.isConstOf ``True then
    return mkConst ``True.intro
  else if let some (p, q) := e.and? then
    let pProof ← buildEqProof p residualOut
    let qProof ← buildEqProof q residualOut
    return mkAndIntro p q pProof qProof
  else if e.isAppOfArity ``Eq 3 then
    let ty  := e.appFn!.appFn!.appArg!
    let lhs := e.appFn!.appArg!
    let rhs := e.appArg!
    let isRfl ←
      try withNewMCtxDepth (isDefEq lhs rhs)
      catch _ => pure false
    if isRfl then
      mkEqRefl ty rhs
    else
      let m ← mkFreshExprMVar (some e) (kind := .syntheticOpaque)
      residualOut.modify (·.push m.mvarId!)
      return m
  else
    -- False or anything else: residual
    let m ← mkFreshExprMVar (some e) (kind := .syntheticOpaque)
    residualOut.modify (·.push m.mvarId!)
    return m

-- ───────────────────────────────────────────────────────────────────────
-- κ-leaf navigation through lam_κᵢ.body[args]
-- ───────────────────────────────────────────────────────────────────────

/-- Walk `lamBody` (a β-reduced sol expression: an ∃-∧-∨ tree ending in an
    Eq-conjunction or False), emitting the proof term that inhabits it.
    Consumes `binders` at ∃-nodes, `guards` at guard-Ands, and `orPath`
    bits at ∨-nodes. -/
private partial def emitKLeaf
    (lamBody : Expr)
    (binders : List (Name × Expr × FVarId))
    (guards  : List (Name × Expr × FVarId))
    (orPath  : List Bool)
    (residualOut : IO.Ref (Array MVarId)) :
    MetaM Expr := do
  -- Or — consume one orPath bit, navigate
  if lamBody.isAppOfArity ``Or 2 then
    let l := lamBody.appFn!.appArg!
    let r := lamBody.appArg!
    match orPath with
    | [] =>
      throwError "emitKLeaf: orPath exhausted at Or-node:{indentExpr lamBody}"
    | false :: restPath =>
      let inner ← emitKLeaf l binders guards restPath residualOut
      return mkOrInl l r inner
    | true :: restPath =>
      let inner ← emitKLeaf r binders guards restPath residualOut
      return mkOrInr l r inner
  -- Exists — consume one binder
  else if lamBody.isAppOfArity ``Exists 2 then
    let α := lamBody.appFn!.appArg!
    let pred := lamBody.appArg!
    match binders with
    | [] =>
      throwError "emitKLeaf: no binders left at Exists-node:{indentExpr lamBody}"
    | (_, _, fvId) :: rest =>
      let witness := mkFVar fvId
      let nextBody := pred.beta #[witness]
      let inner ← emitKLeaf nextBody rest guards orPath residualOut
      mkExistsIntro α pred witness inner
  -- And — distinguish guard-And from Eq-conjunction leaf via guards-emptiness.
  -- Sol1's structure puts all guards before the eq-leaf, so once guards is
  -- empty (and binders/orPath too), any remaining And is the eq-conjunction.
  else if let some (p, q) := lamBody.and? then
    match guards with
    | (_, _, fvId) :: rest =>
      let h := mkFVar fvId
      let inner ← emitKLeaf q binders rest orPath residualOut
      return mkAndIntro p q h inner
    | [] =>
      -- guards exhausted: this And is the eq-conjunction leaf
      buildEqProof lamBody residualOut
  -- Single Eq leaf (κ-arity = 1)
  else if lamBody.isAppOfArity ``Eq 3 then
    buildEqProof lamBody residualOut
  -- True leaf (κ-arity = 0)
  else if lamBody.isConstOf ``True then
    return mkConst ``True.intro
  -- False or unknown: residual
  else
    let m ← mkFreshExprMVar (some lamBody) (kind := .syntheticOpaque)
    residualOut.modify (·.push m.mvarId!)
    return m

-- ───────────────────────────────────────────────────────────────────────
-- Main recursive goal walk
-- ───────────────────────────────────────────────────────────────────────

/-- Walk `goal` (the body of the proof obligation), emitting the proof
    term inline. ∀-binders become λ-abstractions; ∧-splits become
    `And.intro` with `orPath` extended on each branch; κᵢ-headed leaves
    dispatch to `emitKLeaf`; non-κ leaves become residual mvars. -/
partial def walkProof
    (kLams : List (KVar × Expr))
    (goal  : Expr)
    (binders guards : List (Name × Expr × FVarId))
    (orPath : List Bool)
    (residualOut : IO.Ref (Array MVarId)) :
    MetaM Expr := do
  -- (a) κ-headed leaf for one of our κs — check before ∀/∧ since the
  --     leaf is an application, not a binder.
  if let some (_κ, lam, args) := kHead? kLams goal then
    let lamBody := lam.beta args
    return ← emitKLeaf lamBody binders guards orPath residualOut
  -- (b) ∀ — bind, recurse, λ-wrap
  if goal.isForall then
    let dom := goal.bindingDomain!
    let name := goal.bindingName!
    let bi := goal.bindingInfo!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    return ← withLocalDecl name bi dom fun fv => do
      let body := goal.bindingBody!.instantiate1 fv
      let inner ←
        if domSort.isProp then
          walkProof kLams body binders (guards ++ [(name, dom, fv.fvarId!)])
            orPath residualOut
        else
          walkProof kLams body (binders ++ [(name, dom, fv.fvarId!)]) guards
            orPath residualOut
      mkLambdaFVars #[fv] inner
  -- (c) ∧ — split, recurse, And.intro
  if let some (l, r) := goal.and? then
    let pL ← walkProof kLams l binders guards (orPath ++ [false]) residualOut
    let pR ← walkProof kLams r binders guards (orPath ++ [true])  residualOut
    return mkAndIntro l r pL pR
  -- (d) Non-κ leaf — residual mvar
  let m ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
  residualOut.modify (·.push m.mvarId!)
  return m

-- ───────────────────────────────────────────────────────────────────────
-- Top-level elab
-- ───────────────────────────────────────────────────────────────────────

syntax "zapK" : tactic

elab_rules : tactic
  | `(tactic| zapK) => withMainContext do
      -- Phase 1: peel ∃κ binders and compute lam_κᵢ for each κᵢ.
      let goal ← getMainGoal
      let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
      let kctx : KContext := { kvars := kvarMap }
      replaceMainGoal [bodyGoal]
      let mut curr ← (← getMainGoal).getType
      let mut kLams : List (KVar × Expr) := []
      for κ in kvarsInOrder do
        -- Use ZapK-local preserve-And variants so sol's Or-tree mirrors
        -- the goal's full And-tree. (Fusion.lean's `exprScope`/`exprSol1`
        -- strip non-κ branches — fine for solve_fixpoint, wrong for us.)
        let scoped' ← (exprScopePres κ curr).run kctx
        let sol    ← (exprSol1Pres κ scoped').run kctx
        -- Drop dead κ-references from sol (e.g. `(κⱼ y x) ∧ False`)
        -- without collapsing the Or-tree — preserves path-mirror.
        let sol    := simplifyAndExists sol
        let lam    ← solToWitnessExpr sol κ.params κ.paramTypes
        kLams := kLams ++ [(κ, lam)]
        curr   ← (exprElimStar κ sol curr).run kctx

      -- Phase 2: assign each κ-mvar to its lam directly.
      -- (Let-binding UX deferred — would require κ-mvar lctx surgery.)
      for (κ, lam) in kLams do
        κ.mvarId.assign lam

      -- Phase 3: single walk emitting the proof.
      let bodyTy ← (← getMainGoal).getType
      let residualOut ← IO.mkRef #[]
      let proof ← walkProof kLams bodyTy [] [] [] residualOut
      (← getMainGoal).assign proof
      replaceMainGoal (← residualOut.get).toList

-- ───────────────────────────────────────────────────────────────────────
-- Tests (ported from old ZapK.lean)
-- ───────────────────────────────────────────────────────────────────────

/-- ex1-style: single κ, mixed producer/consumer. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zapK
  all_goals first | rfl | grind

/-- ex6-style: two independent κs, four conjuncts. -/
example :
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  zapK
  all_goals first | rfl | grind

/-- ex2-style: two κs with cross-flow. -/
example :
    ∃ κx : Int → Int → Int → Int → Prop, ∃ κy : Int → Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ n : Int,
        n = x - 1 →
        ∀ p : Int,
          p = x + 1 →
          ( (∀ ν : Int, ν = n → κx ν x n p)
          ∧ (∀ ν : Int, ν = p → κy ν x n p)
          ∧ (∀ ν : Int, κx ν x n p → κy ν x n p)
          ∧ (∀ y : Int, κy y x n p →
              ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
          ) := by
  zapK
  all_goals first | rfl | grind
