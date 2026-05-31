import LeanFixpoint.Core
import LeanFixpoint.Fusion.Scope
import LeanFixpoint.Fusion.Sol1

open Lean Meta

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

/-- Split κ-vars into (acyclic, cyclic). The acyclic list is topologically
    sorted so dependency sinks (no κ-deps) appear first — required so each
    κ's sol is built only after its dependencies have been eliminated.

    A κ is cyclic iff it lies on any cycle (`exprIsCyclic`); everything else
    is acyclic and eliminated by fusion. We deliberately do NOT use a minimal
    feedback-vertex cut set (C-J §5.5): cutting only one κ per SCC and fusing
    the *rest* of the SCC inlines the cut κ's mvar into those fused solutions,
    and the resulting constraints handed to PA are too weak to recover the
    invariant (see `comment.lean`, where cutting only `k4` and fusing its
    co-cyclic `k0`/`k5` drops the needed `z1 ≤ z0` on `k4`). Sending every
    SCC member through PA is safe and complete — PA solves the extra κs — so
    over-approximating the cyclic set is the robust choice here. -/
def exprPartitionKVars (e : Expr) : KM (List KVar × List KVar) := do
  let allKs := (← exprKVarsOrdered e).eraseDups
  let deps ← exprDeps e
  let cyclic    ← allKs.filterM (fun κ => exprIsCyclic κ e)
  let acyclicRaw ← allKs.filterM (fun κ => return !(← exprIsCyclic κ e))
  let acyclic := topoSortAcyclic acyclicRaw deps
  return (acyclic, cyclic)


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
