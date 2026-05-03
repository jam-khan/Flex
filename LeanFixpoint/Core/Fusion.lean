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
  if let some (l, r) := e.and? then
    let inL := (← KM.exprKVars l).contains κ
    let inR := (← KM.exprKVars r).contains κ
    if inL && !inR then exprScope κ l
    else if !inL && inR then exprScope κ r
    else return e
  else if e.isForall then
    let dom := e.bindingDomain!
    if !(← KM.exprKVars dom).contains κ then
      withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
        let sc ← exprScope κ (e.bindingBody!.instantiate1 fvar)
        let abstr := sc.abstract #[fvar]
        pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
    else
      return e
  else
    return e

/-- `sol1(κ, e)` — strongest solution (Section 5.2).
    Maps: `And → Or`, `∀(Prop) → And`, `∀(non-Prop) → ∃`, leaf κ-app → equality. -/
partial def exprSol1 (κ : KVar) (e : Expr) (simplify := false) : KM Expr := do
  let raw ← sol1Aux e
  if simplify then return simplifyExpr raw else return raw
where
  sol1Aux (e : Expr) : KM Expr := do
    let e ← whnf e
    if let some (l, r) := e.and? then
      return mkApp2 (mkConst ``Or) (← sol1Aux l) (← sol1Aux r)
    else if e.isForall then
      let name := e.bindingName!
      let dom  := e.bindingDomain!
      withLocalDeclD name dom fun fvar => do
        let body := e.bindingBody!.instantiate1 fvar
        let domSort ← (inferType dom >>= whnf : MetaM Expr)
        if domSort.isProp then
          -- Prop domain: conjoin hypothesis
          let inner := mkApp2 (mkConst ``And) dom (← sol1Aux body)
          let abstrBody := inner.abstract #[fvar]
          if abstrBody.hasLooseBVars then
            let lam := Expr.lam name dom abstrBody .default
            return mkApp2 (mkConst ``Exists [levelZero]) dom lam
          else
            return inner
        else
          -- Non-Prop domain: recurse, wrap with ∃ if variable is used
          let inner ← sol1Aux body
          let abstrBody := inner.abstract #[fvar]
          if abstrBody.hasLooseBVars then
            let lam := Expr.lam name dom abstrBody .default
            return mkApp2 (mkConst ``Exists [levelOne]) dom lam
          else
            return inner
    else
      -- Leaf: check if κ-application
      if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
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

/-- Compute solution with scope stripping.
    Opens scope `∀`-binders inside `withLocalDeclD`, computes `sol1` there,
    and replaces scope fvars with canonical κ-params before returning.
    Only non-Prop binders are added to `scopeInfo` for param replacement. -/
partial def computeSolStripped (κ : KVar) (e : Expr) (simplify : Bool)
    (scopeInfo : List (Expr × Name) := []) : KM (Expr × List Name) := do
  let e ← whnf e
  if e.isForall then
    let dom := e.bindingDomain!
    if !(← KM.exprKVars dom).contains κ then
      let domSort ← (inferType dom >>= whnf : MetaM Expr)
      withLocalDeclD e.bindingName! dom fun fvar => do
        if domSort.isProp then
          -- Prop guard: strip but don't add to scopeInfo
          computeSolStripped κ (e.bindingBody!.instantiate1 fvar) simplify scopeInfo
        else
          -- Value binder: strip and add to scopeInfo
          computeSolStripped κ (e.bindingBody!.instantiate1 fvar) simplify
            (scopeInfo ++ [(fvar, e.bindingName!)])
    else
      -- Domain contains κ → stop stripping, compute sol1 here
      finalizeSol κ e simplify scopeInfo
  else
    -- No forall at top level (e.g., And) → stop stripping
    finalizeSol κ e simplify scopeInfo
where
  /-- Given all κ-app arg arrays, locate which κ-arg position `scopeFV`
      appears in bare. Prefer a position where it appears bare in EVERY
      κ-app; if no such universal position exists, fall back to the
      last bare occurrence across all calls. Returns `none` if the scope
      fvar never appears as a bare argument. -/
  resolveScopeParam (κ : KVar) (allArgs : List (Array Expr))
      (scopeFV : Expr) : Option Name :=
    -- Find positions where scopeFV appears bare in EACH κ-app (as a set).
    let perCall : List (List Nat) :=
      allArgs.map fun args =>
        (List.range args.size).filter fun i => args[i]? == some scopeFV
    -- Universal positions: present in every call.
    let universal : List Nat :=
      match perCall with
      | [] => []
      | first :: rest =>
        first.filter fun i => rest.all (·.contains i)
    let chosen : Option Nat :=
      match universal with
      | i :: _ => some i
      | []     =>
        -- No universal position: pick the last bare occurrence overall.
        let all := perCall.flatten
        all.foldl (fun _acc i => some i) (none : Option Nat)
    match chosen with
    | some idx => κ.params[idx]?
    | none     => none
  finalizeSol (κ : KVar) (e : Expr) (simplify : Bool)
      (scopeInfo : List (Expr × Name)) : KM (Expr × List Name) := do
    let sol ← exprSol1 κ e simplify
    let scopeNames := scopeInfo.map (·.2)
    if scopeInfo.isEmpty then return (sol, scopeNames)
    -- Legacy fallback: last-N positional mapping, but only if type-compatible.
    let numRefParams := κ.params.length - scopeInfo.length
    let legacyParams := κ.params.drop numRefParams
    let legacyTypes  := κ.paramTypes.drop numRefParams
    -- Collect κ-apps once; reuse for all scope vars.
    let allArgs := collectKAppArgs κ e
    -- For each scope fvar: try to find its bare-arg position; fall back to
    -- legacy-positional only if the types agree. Otherwise leave unsubstituted.
    let resolved : List (Option Name) ←
      (scopeInfo.zip (legacyParams.zip legacyTypes)).mapM
        fun ((scopeFV, _), (legacy, legacyTy)) => do
          match resolveScopeParam κ allArgs scopeFV with
          | some p => pure (some p)
          | none =>
            let scopeTy ← inferType scopeFV
            if ← isDefEq scopeTy legacyTy then
              pure (some legacy)
            else
              pure none
    let sFixed := (scopeInfo.zip resolved).foldl
      (fun acc ((scopeFV, _), mParam) =>
        match mParam with
        | some paramName => acc.replaceFVar scopeFV (.fvar (FVarId.mk paramName))
        | none           => acc) sol
    return (sFixed, scopeNames)

/-- Compute solution for κ, deciding whether to use scope stripping or full `sol1`. -/
def computeSol (κ : KVar) (fullConstraint : Expr) (simplify := false) : KM (Expr × List Name) := do
  let sc ← exprScope κ fullConstraint
  let nScope ← countScopeVars κ sc
  if nScope > 0 && κ.params.length > nScope then
    computeSolStripped κ sc simplify
  else
    let sol ← exprSol1 κ fullConstraint simplify
    return (sol, [])

/-- Single κ elimination: compute solution then substitute. -/
def exprElim1 (κ : KVar) (e : Expr) : KM Expr := do
  let (sol, _) ← computeSol κ e
  exprElimStar κ sol e

/-- Eliminate multiple κ-variables sequentially. -/
def exprElim (kvars : List KVar) (e : Expr) : KM Expr := do
  let mut acc := e
  for κ in kvars do
    acc ← exprElim1 κ acc
  return acc



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
