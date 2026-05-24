import LeanFixpoint.Fusion.Types
import LeanFixpoint.Monad
import LeanFixpoint.Fusion.Utils
import LeanFixpoint.Fusion.Flatten
import LeanFixpoint.Fusion.Graph

open Lean Meta

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
  -- let e ← whnf e
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
    -- scope(κ, cₗ ∧ cᵣ) — preserve full And-structure (no stripping).
  -- Stripping breaks zapk's path-duality (path counts inLs/inRs based on c's
  -- And-tree, sol's Or-tree must mirror it exactly). Semantic equivalence
  -- is preserved: non-κ branches reduce to ⊥-leaves via sol1's catch-all,
  -- and downstream simplifyExpr collapses `∨ ⊥` for tactics that use it.
  -- if e.and?.isSome then
  --   return e

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

/-- `scope(κ, e)` — extract the sub-expression relevant to κ (Fig. 9). -/
partial def exprScopeZapK (κ : KVar) (e : Expr) : KM Expr := do
  -- let e ← whnf e
  -- scope(κ, cₗ ∧ cᵣ)
  -- scope(κ, cₗ ∧ cᵣ) — preserve full And-structure (no stripping).
  -- Stripping would break zapk's path-mirror (the path's inL/inR sequence
  -- must match sol's Or-tree exactly). Sol1's And-handling recurses into
  -- both sides; non-κ branches reduce to False leaves via sol1's catch-all.
  if e.and?.isSome then
    return e

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

/-- Smart `And`: `(_ ∧ False) = (False ∧ _) = False`, `(_ ∧ True) = _`.
    Mirrors liquid-fixpoint's empty-cube absorption: when the inner sol1 is
    `False`, the binder predicate above it is dropped, so dead κ-references
    that would survive under `∧ False` never get built into the Expr. -/
private def mkAndSmart (l r : Expr) : Expr :=
  if l.isConstOf ``False || r.isConstOf ``False then mkConst ``False
  else if l.isConstOf ``True then r
  else if r.isConstOf ``True then l
  else mkApp2 (mkConst ``And) l r

/-- Smart `Or`: drops `False`, absorbs `True`. -/
private def mkOrSmart (l r : Expr) : Expr :=
  if l.isConstOf ``True || r.isConstOf ``True then mkConst ``True
  else if l.isConstOf ``False then r
  else if r.isConstOf ``False then l
  else mkApp2 (mkConst ``Or) l r


/-
sol1(κ, c₁ ∧ c₂)        ≡ sol1(κ, c₁) ∨ sol1(κ, c₂)
sol1(κ, ∀ x:b. p ⇒ c)   ≡ ∃x:b. p ∧ sol1(κ, c)
sol1(κ, κ(y₁, ..., yₙ)) ≡ x₁ = y₁ ∧ ... ∧ xₙ = yₙ
sol1(κ, p)              ≡ false
-/
/-- `sol1(κ, e)` — strongest solution (Section 5.2).
    Maps: `And → Or`, `∀(Prop) → And`, `∀(non-Prop) → ∃`, leaf κ-app → equality.
    Uses `mkAndSmart`/`mkOrSmart` and drops the ∃-wrap when the conjunct collapses
    to `False`, mirroring liquid-fixpoint's `first (b :) <$> [] = []` absorption. -/
partial def exprSol1 (κ : KVar) (e : Expr) : KM Expr := do
  -- let e ← whnf e
  let e ← exprScope κ e
  -- c₁ ∧ c₂
  if let some (l, r) := e.and? then
    return mkOrSmart (← exprSol1 κ l) (← exprSol1 κ r)
  -- ∀ x : b. p ⇒ c
  else if e.isForall then
    let name := e.bindingName!
    let dom := e.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp then
      -- Bare implication `p ⇒ c`. Algorithm: emit p ∧ sol1(c) with no ∃ wrap,
      -- since there's no value binder at this level. The Prop binder is
      -- conventionally unused, but instantiate via withLocalDeclD just in case.
      return ← withLocalDeclD name dom fun pfvar => do
        let body ← whnf (e.bindingBody!.instantiate1 pfvar)
        let inner ← exprSol1 κ body
        return mkAndSmart dom inner

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
                return mkAndSmart p inner
            else
              exprSol1 κ body
          else
            exprSol1 κ body
        -- If the conjunct collapsed to False, drop the ∃ wrapper too —
        -- this is the Expr-level analog of `first (b :) <$> [] = []`.
        if conjunct.isConstOf ``False then
          return mkConst ``False
        let abstr := conjunct.abstract #[fvar]
        let lam   := Expr.lam name dom abstr .default
        return mkApp2 (mkConst ``Exists [levelOne]) dom lam
  -- κ(y₁, ..., yₙ)
  else if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
    let args := e.getAppArgs.toList
    -- Build each equality `zᵢ = aᵢ`, but drop tautologies (`zᵢ = zᵢ`) that arise
    -- when `stripScopePrefix` has already substituted the outer binder into `aᵢ`.
    let eqs := (κ.params.zip (args.zip κ.paramTypes)).filterMap fun (pi, (ai, ty)) =>
      let lhs : Expr := .fvar (FVarId.mk pi)
      if lhs == ai then none
      else some (mkApp3 (mkConst ``Eq [levelOne]) ty lhs ai)
    match eqs with
    | []      => return mkConst ``True
    | [eq]    => return eq
    | eq :: rest => return rest.foldl mkAndSmart eq
  else
    return mkConst ``False

/-- `elim*(κ, sol, e)` — substitute κ with its solution throughout `e` (Fig. 11).
    Head-position κ-apps become `True`; hypothesis-position κ-apps get `substKVarInExpr`. -/
partial def exprElimStar (κ : KVar) (sol : Expr) (e : Expr) : KM Expr := do
  -- let e ← whnf e
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
  -- let e ← whnf e
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

/-- Find a κ-param position that `binderFvar` *consistently* fills across all
    κ-applications in `body`.

    For each κ-app, collect the set of positions where `binderFvar` appears.
    Then the **universal positions** are those present in *every* κ-app's set.
    If any universal position exists, return the smallest. Otherwise, fall back
    to the last bare occurrence across all calls (legacy compatibility with the
    pre-mvar-migration `resolveScopeParam`).

    This tolerates binders that appear at multiple positions within a single
    κ-app (common in FluxRS-generated VCs where the same value is passed both
    as a base param and as a `.elems`/`.len` accessor target). -/
def findOuterBinderToParam (κ : KVar) (binderFvar : FVarId) (body : Expr) : Option Nat :=
  let kArgsList := collectKAppArgs κ body
  let perCall : List (List Nat) := kArgsList.map fun args =>
    (List.range args.size).filter fun i => args[i]! == .fvar binderFvar
  let universal : List Nat :=
    match perCall with
    | []           => []
    | first :: rest => first.filter fun i => rest.all (·.contains i)
  match universal with
  | i :: _ => some i
  | []     =>
    -- No universal position: fall back to last bare occurrence overall.
    perCall.flatten.foldl (fun _ i => some i) (none : Option Nat)

/-- `exprSolScoped κ e` — strip the κ-free outer ∀-prefix and compute sol1
    on the inner `c'`, returning the paper's σ̂_body.

    Behavior per outer ∀:
    - **Type binder** `∀ x:T. body` — if `x` is consistently the i-th κ-arg,
      record `(x_fvar, zᵢ)` to be substituted in the final sol. Otherwise
      stop stripping and treat from this binder as part of `c'`.
    - **Prop binder** `∀ _:p. body` (implication antecedent) — drop `p` and
      descend (the hypothesis is in scope at every κ-use site, so the sol
      doesn't repeat it).
    - **κ-containing dom or non-∀** — `c'` starts here.

    *Substitution is deferred*: we walk through `withLocalDeclD` keeping REAL
    fvars in scope so that `exprSol1`'s `inferType`/`whnf` on sub-expressions
    succeed (synthetic `FVarId.mk "zᵢ"` would fail since they're not in the
    local context). Only AFTER sol1 builds the final sol do we substitute
    each recorded fvar with its synthetic κ-param fvar — that substitution
    is the analog of `solToWitnessExpr`'s param→fvar mapping. -/
partial def exprSolScoped (κ : KVar) (e : Expr) : KM Expr :=
  goStrip κ e []
where
  /-- Descend through the outer prefix, accumulating
      `(fvar, paramName)` pairs of bindings we'll substitute on the final sol. -/
  goStrip (κ : KVar) (e : Expr) (acc : List (FVarId × Name)) : KM Expr := do
    if e.isForall then
      let dom := e.bindingDomain!
      if (← KM.exprKVars dom).contains κ then
        finalize κ e acc
      else
        let domSort ← (inferType dom >>= whnf : MetaM Expr)
        withLocalDeclD e.bindingName! dom fun fvar => do
          let body := e.bindingBody!.instantiate1 fvar
          if domSort.isProp then
            goStrip κ body acc
          else
            match findOuterBinderToParam κ fvar.fvarId! body with
            | some i =>
              let paramName := κ.params[i]!
              goStrip κ body (acc ++ [(fvar.fvarId!, paramName)])
            | none =>
              -- Stop stripping. Re-close `fvar` so c' is well-formed (no
              -- dangling fvar after we exit this `withLocalDeclD`), then
              -- hand off to finalize.
              let bodyClosed := body.abstract #[fvar]
              let cPrime := Expr.forallE e.bindingName! dom bodyClosed e.bindingInfo!
              finalize κ cPrime acc
    else
      finalize κ e acc

  /-- Build sol1 with REAL outer fvars in scope, then substitute each recorded
      fvar with its synthetic κ-param fake-fvar. -/
  finalize (κ : KVar) (cPrime : Expr) (acc : List (FVarId × Name)) : KM Expr := do
    let sol ← exprSol1 κ cPrime
    return acc.foldl
      (fun s (fvarId, paramName) =>
        s.replaceFVar (.fvar fvarId) (.fvar (FVarId.mk paramName)))
      sol


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
  let sol     ← exprSolScoped κ scoped'
  let newE    ← exprElimStar κ sol e
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
    κ's sol is built only after its dependencies have been eliminated.

    Uses `classifyKVars` (C-J §5.5 cut-set approach): compute SCCs, designate
    a minimal cut set as cyclic, and treat *the rest as acyclic in the reduced
    graph*. Per-κ `exprIsCyclic` would wrongly flag every member of a
    cycle's transitive closure as cyclic. -/
def exprPartitionKVars (e : Expr) : KM (List KVar × List KVar) := do
  let allKs := (← exprKVarsOrdered e).eraseDups
  let deps ← exprDeps e
  return classifyKVars allKs deps
