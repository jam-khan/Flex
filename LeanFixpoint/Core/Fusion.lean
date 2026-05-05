import LeanFixpoint.Core.Types
import LeanFixpoint.Monad
import LeanFixpoint.Core.Utils
import LeanFixpoint.Core.Fusion.Flatten
import LeanFixpoint.Core.Fusion.Graph

open Lean Meta

-- Replace κ(arg₁, ..., argₙ) with sol[z₀ := arg₁, ..., zₙ := argₙ]
def substKVarInExpr (κ : KVar) (sol : Expr) (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.getAppFn.isMVar && sub.getAppFn.mvarId! == κ.mvarId then
      let args := sub.getAppArgs
      let result := (κ.params.zip args.toList).foldl
        (fun acc (param, arg) => acc.replaceFVar (.fvar (FVarId.mk param)) arg) sol
      some result
    else none

/-! ## Expr-direct fusion functions

  These operate directly on `Lean.Expr` instead of the `Constraint` AST.
  Each `∀`-binder is processed with `withLocalDeclD` to create temporary fvars,
  then `Expr.abstract` re-closes them before returning.

  Mapping from `Constraint` constructors to `Expr` patterns:
  - `.pred e`         → any `Expr` that is not `And` and not `forallE`
  - `.conj c₁ c₂`    → `e.and? = some (l, r)`
  - `.imp x τ p fv c` → `e.isForall`
-/

/-- `scope(κ, e)` — extract the sub-expression relevant to κ (Fig. 9). -/
partial def exprScope (κ : KVar) (e : Expr) : KM Expr := do
  let e ← whnf e
  -- scope(κ, cₗ ∧ cᵣ)
  if let some (cₗ, cᵣ) := e.and? then
    let inL := (← KM.exprKVars cₗ ).contains κ
    let inR := (← KM.exprKVars cᵣ).contains κ
    -- κ ∈ Cₗ, κ ∉ Cᵣ
    if inL && !inR
      then exprScope κ cₗ
    -- κ ∉ Cₗ, κ ∈ Cᵣ
    else if !inL && inR
      then exprScope κ cᵣ
    -- fallback: scope(κ, c) = c
    else return e
  -- scope(κ, ∀ x : τ. body)
  -- Handles one forall at a time. The paper's `∀x:b. p ⇒ c'` pattern
  -- is two nested foralls, so this branch fires twice (once with dom = b,
  -- once with dom = p) — together that enforces κ ∉ p.
  else if e.isForall then
    let dom := e.bindingDomain!
    if !(← KM.exprKVars dom).contains κ then
      withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
        let sc ← exprScope κ (e.bindingBody!.instantiate1 fvar)
        let abstr := sc.abstract #[fvar]
        pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
    else
      return mkConst ``False
  else
    return e

/-
sol1(κ, c₁ ∧ c₂)        ≡ sol1(κ, c₁) ∨ sol1(κ, c₂)
sol1(κ, ∀ x:b. p ⇒ c)   ≡ ∃x:b. p ∧ sol1(κ, c)
sol1(κ, κ(y₁, ..., yₙ)) ≡ x₁ = y₁ ∧ ... ∧ xₙ = yₙ
sol1(κ, p)              ≡ false
-/
/-- `sol1(κ, e)` — strongest solution (Section 5.2).
    Maps: `And → Or`, `∀(Prop) → And`, `∀(non-Prop) → ∃`, leaf κ-app → equality. -/
partial def exprSol1 (κ : KVar) (e : Expr) : KM Expr := do
  let e ← whnf e
  let e ← exprScope κ e
  -- c₁ ∧ c₂
  if let some (l, r) := e.and? then
    return mkApp2 (mkConst ``Or) (← exprSol1 κ l) (← exprSol1 κ r)
  -- ∀ x : b. p ⇒ c
  else if e.isForall then
    let name := e.bindingName!
    let dom := e.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp then
      -- Bare implication at this level shouldn't appear --
      -- implications are always handled inline by the value-binder below.
      -- Throw to catch malformed input early.
      throwError "sol1: bare implication outside enclosing value binder: \
        ∀ _ : {← ppExpr dom}, ⋯"
    else
      -- ∀ x:b. body -- open x, and boyd is expected to be 'p ⇒ c'
      return ← withLocalDeclD name dom fun fvar => do
        let body ← whnf (e.bindingBody!.instantiate1 fvar)
        let conjunct ← do
          if body.isForall then
            let p := body.bindingDomain!
            let pSort ← (inferType p >>= whnf : MetaM Expr)
            if pSort.isProp then
              -- Inline implication handling: extract p and c', recurse on c'
              -- Implication binder is unused; but introducing fresh fvar just in case
              withLocalDeclD body.bindingName! p fun pfvar => do
                let c'  := body.bindingBody!.instantiate1 pfvar
                let inner ← exprSol1 κ c'
                return mkApp2 (mkConst ``And) p inner
            else
              exprSol1 κ body
          else
            exprSol1 κ body
        -- Wrap ∃ x : b.
        let abstr := conjunct.abstract #[fvar]
        let lam   := Expr.lam name dom abstr .default
        return mkApp2 (mkConst ``Exists [levelOne]) dom lam
  -- κ(y₁, ..., yₙ)
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

/-- `elim*(κ, sol, e)` — substitute κ with its solution throughout `e` (Fig. 11).
    Head-position κ-apps become `True`; hypothesis-position κ-apps get `substKVarInExpr`. -/
partial def exprElimStar (κ : KVar) (sol : Expr) (e : Expr) : KM Expr := do
  let e ← whnf e
  if let some (l, r) := e.and? then
    let l' ← exprElimStar κ sol l
    let r' ← exprElimStar κ sol r
    return mkApp2 (mkConst ``And) l' r'
  else if e.isForall then
    withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
      let dom'  := substKVarInExpr κ sol e.bindingDomain!
      let body  := e.bindingBody!.instantiate1 fvar
      let body' ← exprElimStar κ sol body
      let abstr := body'.abstract #[fvar]
      pure (Expr.forallE e.bindingName! dom' abstr e.bindingInfo!)
  else
    -- Leaf (conclusion position)
    if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
      return mkConst ``True
    else
      return substKVarInExpr κ sol e

/-- Count scope variables: outer non-Prop `∀`-binders whose domains don't mention κ.
    Only value binders (non-Prop domains like `Int`) are counted — Prop guards
    (like `0 ≤ x →`) are skipped but not counted, matching the original
    `Constraint.imp` behavior where each imp bundled a type binder with its guard. -/
partial def countScopeVars (κ : KVar) (e : Expr) : KM Nat := do
  let e ← whnf e
  if e.isForall then
    let dom := e.bindingDomain!
    if !(← KM.exprKVars dom).contains κ then
      let domSort ← (inferType dom >>= whnf : MetaM Expr)
      withLocalDeclD e.bindingName! dom fun fvar => do
        let rest ← countScopeVars κ (e.bindingBody!.instantiate1 fvar)
        if domSort.isProp then
          -- Prop guard: strip but don't count
          return rest
        else
          -- Value binder: count as scope var
          return 1 + rest
    else return 0
  else return 0

/-- Collect ALL κ-applications in `e`, returning a list of their argument arrays.
    Skips into inner binders without instantiating, so args may contain loose bvars.
    The caller should filter for args matching intended free variables. -/
partial def collectKAppArgs (κ : KVar) (e : Expr) : List (Array Expr) :=
  let hit : List (Array Expr) :=
    if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then [e.getAppArgs]
    else []
  let rec childArgs (e : Expr) : List (Array Expr) :=
    collectKAppArgs κ e
  let childHits : List (Array Expr) :=
    match e with
    | .app f a         => childArgs f ++ childArgs a
    | .forallE _ d b _ => childArgs d ++ childArgs b
    | .lam _ d b _     => childArgs d ++ childArgs b
    | .letE _ t v b _  => childArgs t ++ childArgs v ++ childArgs b
    | .mdata _ e'      => childArgs e'
    | .proj _ _ e'     => childArgs e'
    | _                => []
  hit ++ childHits


/-- `elim1(κ, c)` per Cosman & Jhala 2017 §5.3 (Fig. 11).
    Returns `(σ̂_body, elim*(σ̂, c))`:
      - `σ̂_body` = `sol1(κ, scope(κ, c))`, the body of the scoped solution.
        This is what you wrap as `λx̄. σ̂_body` to assign to κ-mvar.
      - `elim*(σ̂, c)` is the constraint with κ-uses substituted away.

    Caller is responsible for assigning κ-mvar AFTER consuming the new
    constraint — never before, or `whnf` will eagerly expand `?κ` and the
    next iteration's elim1 will see no raw `?κ` to substitute. -/
-- CHECK THIS
def exprElim1 (κ : KVar) (e : Expr) : KM (Expr × Expr) := do
  let scoped' ← exprScope κ e
  let sol    ← exprSol1 κ scoped'
  -- extra simplification added
  -- let sol   := simplifyExpr sol
  let newE   ← exprElimStar κ sol e
  return (sol, newE)

-- CHECK THIS
def exprElim (kvars : List KVar) (e : Expr) : KM (List (KVar × Expr) × Expr) := do
  let mut acc := e
  let mut sols : List (KVar × Expr) := []
  for κ in kvars do
    let (sol, acc') ← exprElim1 κ acc
    sols := sols ++ [(κ, sol)]
    acc := acc'
  return (sols, acc)

/-- Split κ-vars into (acyclic, cyclic). The acyclic list is topologically
    sorted so dependency sinks (no κ-deps) appear first — required so each
    κ's sol is built only after its dependencies have been eliminated. -/
def exprPartitionKVars (e : Expr) : KM (List KVar × List KVar) := do
  let allKs := (← exprKVarsOrdered e).eraseDups
  let cuts ← allKs.filterM (fun κ => exprIsCyclic κ e)
  let acyclicRaw ← allKs.filterM (fun κ => return !(← exprIsCyclic κ e))
  let deps ← exprDeps e
  let acyclic := topoSortAcyclic acyclicRaw deps
  return (acyclic, cuts)
