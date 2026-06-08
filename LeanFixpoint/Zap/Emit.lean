import Lean
import LeanFixpoint.Core

open Lean Meta Elab Tactic

-- Creates a proof for `∃ x : α, p x`
def mkExistsIntro (α predLam w proof : Expr) : MetaM Expr := do
  let u ← getLevel α
  return mkApp4 (mkConst ``Exists.intro [u]) α predLam w proof

-- Creates a proof for `a ∧ b`
def mkAndIntro (a b ha hb : Expr) : Expr :=
  mkApp4 (mkConst ``And.intro) a b ha hb

-- Creates a left-injection proof for `a ∨ b`
def mkOrInl (a b h : Expr) : Expr :=
  mkApp3 (mkConst ``Or.inl) a b h

-- Creates right-injection proof for `a ∨ b`
def mkOrInr (a b h : Expr) : Expr :=
  mkApp3 (mkConst ``Or.inr) a b h

-- Creates a proof for `x = x`
def mkEqRefl (ty x : Expr) : MetaM Expr := do
  let u ← getLevel ty
  return mkApp2 (mkConst ``Eq.refl [u]) ty x

/-
  Build a proof of an Eq / And-of-Eqs / True / False expression.
  Eq leaves auto-discharge via `isDefEq` when LHS/RHS are syntactically
  equal up to defeq (the common case: every eq comes from `zᵢ = aᵢ` where
  both sides reduce to the same value-binder fvar). Non-rfl eqs and
  `False` leaves become residual mvars.
-/
partial def buildEqProof
  (e : Expr)
  (residualOut : IO.Ref (Array MVarId)) : MetaM Expr := do

    if e.isConstOf ``True then return mkConst ``True.intro

    else if let some (p, q) := e.and? then
      let pProof ← buildEqProof p residualOut
      let qProof ← buildEqProof q residualOut
      return mkAndIntro p q pProof qProof

    else if e.isAppOfArity ``Eq 3 then
      let ty  := e.appFn!.appFn!.appArg!
      let lhs := e.appFn!.appArg!
      let rhs := e.appArg!
      let isRfl ←
        try
          withNewMCtxDepth (isDefEq lhs rhs)
        catch _ =>
          pure false
      if isRfl then mkEqRefl ty rhs
      else
        let m ← mkFreshExprMVar (some e) (kind := .syntheticOpaque)
        residualOut.modify (·.push m.mvarId!)
        return m
    else
      let m ← mkFreshExprMVar (some e) (kind := .syntheticOpaque)
      residualOut.modify (·.push m.mvarId!)
      return m

/-- Walk `lamBody` (a β-reduced sol expression: an ∃-∧-∨ tree ending in an
    Eq-conjunction or False), emitting the proof term that inhabits it.
    Consumes `binders` at ∃-nodes, `guards` at guard-Ands, and `orPath`
    bits at ∨-nodes. -/
partial def emitKLeaf
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

/-- Collapse inert structure (`False ∨ _`, `_ ∨ False`, `True ∧ _`, `_ ∧ True`,
    `False ∧ _`, `_ ∧ False`, `True ∨ _`, `_ ∨ True`) in a proposition `e`,
    recursing through `∧ ∨ ∃ ∀ →` with the core congruence lemmas. Returns
    `(clean, iff)` with `iff : e ↔ clean`.

    This is a single structural pass — unlike `simp`, it never iterates to a
    fixpoint, so it survives the deep nesting of the structure-preserving residual
    that overflows `simp`'s recursion. Implications `D → C` clean the hypothesis
    `D` too (via `imp_congr`), which is essential because the deepest noise lives
    in the σ̂ hypotheses. Use `iff.mpr` to discharge the original (noisy) goal from
    a proof of `clean`. -/
partial def collapseInert (e : Expr) : MetaM (Expr × Expr) := do
  if e.isAppOfArity ``And 2 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', ia) ← collapseInert a
    let (b', ib) ← collapseInert b
    let cg ← mkAppM ``and_congr #[ia, ib]                  -- (a∧b) ↔ (a'∧b')
    if a'.isConstOf ``False then
      return (mkConst ``False,
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``false_and #[b']]])
    else if b'.isConstOf ``False then
      return (mkConst ``False,
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``and_false #[a']]])
    else if a'.isConstOf ``True then
      return (b',
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``true_and #[b']]])
    else if b'.isConstOf ``True then
      return (a',
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``and_true #[a']]])
    else if a' == a && b' == b then
      return (e, ← mkAppM ``Iff.refl #[e])
    else
      return (← mkAppM ``And #[a', b'], cg)
  else if e.isAppOfArity ``Or 2 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', ia) ← collapseInert a
    let (b', ib) ← collapseInert b
    let cg ← mkAppM ``or_congr #[ia, ib]                   -- (a∨b) ↔ (a'∨b')
    if a'.isConstOf ``True then
      return (mkConst ``True,
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``true_or #[b']]])
    else if b'.isConstOf ``True then
      return (mkConst ``True,
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``or_true #[a']]])
    else if a'.isConstOf ``False then
      return (b',
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``false_or #[b']]])
    else if b'.isConstOf ``False then
      return (a',
        ← mkAppM ``Iff.trans #[cg, ← mkAppM ``Iff.of_eq #[← mkAppM ``or_false #[a']]])
    else if a' == a && b' == b then
      return (e, ← mkAppM ``Iff.refl #[e])
    else
      return (← mkAppM ``Or #[a', b'], cg)
  else if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam nm dom body bi =>
      withLocalDeclD nm dom fun fv => do
        let bodyInst := body.instantiate1 fv
        let (body', ib) ← collapseInert bodyInst
        if body' == bodyInst then
          return (e, ← mkAppM ``Iff.refl #[e])
        let hMot ← mkLambdaFVars #[fv] ib                  -- ∀ x, body x ↔ body' x
        let cg ← mkAppM ``exists_congr #[hMot]
        let cleanPred := Expr.lam nm dom (body'.abstract #[fv]) bi
        return (← mkAppM ``Exists #[cleanPred], cg)
    | _ => return (e, ← mkAppM ``Iff.refl #[e])
  else if e.isForall then
    let dom  := e.bindingDomain!
    let body := e.bindingBody!
    let nm   := e.bindingName!
    let bi   := e.bindingInfo!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp && !body.hasLooseBVar 0 then
      -- Non-dependent implication `D → C`: clean the hypothesis `D` too.
      let (d', iD) ← collapseInert dom
      let (c', iC) ← collapseInert body
      let cg ← mkAppM ``imp_congr #[iD, iC]                 -- (D→C) ↔ (D'→C')
      if c'.isConstOf ``True then
        -- `D' → True` ↔ True  (eliminated-head conclusion)
        return (mkConst ``True, ← mkAppM ``Iff.trans #[cg, ← mkAppM ``imp_true_iff #[d']])
      else if d' == dom && c' == body then
        return (e, ← mkAppM ``Iff.refl #[e])
      else
        return (Expr.forallE nm d' c' bi, cg)
    else
      -- Value binder (or dependent ∀): clean the body.
      withLocalDeclD nm dom fun fv => do
        let bodyInst := body.instantiate1 fv
        let (body', ib) ← collapseInert bodyInst
        if body' == bodyInst then
          return (e, ← mkAppM ``Iff.refl #[e])
        let hMot ← mkLambdaFVars #[fv] ib
        let cg ← mkAppM ``forall_congr' #[hMot]
        if body'.isConstOf ``True then
          -- `∀ x, True` ↔ True
          return (mkConst ``True, ← mkAppM ``Iff.trans #[cg, ← mkAppM ``imp_true_iff #[dom]])
        else
          return (Expr.forallE nm dom (body'.abstract #[fv]) bi, cg)
  else
    return (e, ← mkAppM ``Iff.refl #[e])

