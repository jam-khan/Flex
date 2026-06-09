import LeanFixpoint.Fusion.Strip
import LeanFixpoint.Zap.Sol1

open Lean Meta

/-- Structure-preserving scoped solution + prefix metadata for the
    path-informed walk. `sol` is LCA-scoped param-form (no extra `∃`/guards
    above the LCA); the counts tell `walkPhase5` how many accumulated
    binders/guards/orPath bits to `drop` at each κ-leaf. -/
structure ScopedSolPres where
  sol      : Expr
  nBinders : Nat    -- prefix value-binders above the LCA  (→ κ-params)
  nGuards  : Nat    -- prefix Prop-guards above the LCA     (dropped)
  nOr      : Nat    -- one-sided `∧` routings above the LCA (→ orPath bits)
  deriving Inhabited

/-- `exprSolScopedPres κ e` — the structure-preserving analog of
    `exprSolScoped`. Descends the κ-free prefix through `∀`-binders **and**
    one-sided `∧` routings, param-matching value binders and counting the
    prefix, stops at the LCA (first `∧` with κ in both branches, or a κ-leaf,
    or a non-mapping value binder), and runs `exprSol1Pres` there so the
    below-LCA `∧`↔`∨` mirror survives for `walkPhase5`/`emitKLeaf`.

    Mirrors `exprSolScoped` (Strip.lean) verbatim apart from: the `∧`-routing
    branch, the `(nB,nG,nOr)` prefix counters, and `exprSol1Pres` (preserving)
    in `finalize` instead of `exprSol1` (branch-stripping). -/
partial def exprSolScopedPres (κ : KVar) (e : Expr) : KM ScopedSolPres :=
  goStrip κ e [] 0 0 0
where
  goStrip (κ : KVar) (e : Expr) (acc : List (FVarId × Name))
      (nB nG nOr : Nat) : KM ScopedSolPres := do
    -- ∧ routing: descend the unique κ-branch; κ in both ⇒ LCA, stop here.
    if let some (l, r) := e.and? then
      let lHas := (← KM.exprKVars l).contains κ
      let rHas := (← KM.exprKVars r).contains κ
      if lHas && !rHas then
        goStrip κ l acc nB nG (nOr + 1)
      else if rHas && !lHas then
        goStrip κ r acc nB nG (nOr + 1)
      else
        finalize κ e acc nB nG nOr
    else if e.isForall then
      let dom := e.bindingDomain!
      if (← KM.exprKVars dom).contains κ then
        finalize κ e acc nB nG nOr
      else
        let domSort ← (inferType dom >>= whnf : MetaM Expr)
        withLocalDeclD e.bindingName! dom fun fvar => do
          let body := e.bindingBody!.instantiate1 fvar
          if domSort.isProp then
            goStrip κ body acc nB (nG + 1) nOr
          else
            match findOuterBinderToParam κ fvar.fvarId! body with
            | some i =>
              goStrip κ body (acc ++ [(fvar.fvarId!, κ.params[i]!)]) (nB + 1) nG nOr
            | none =>
              -- stop-strip: re-close fvar; this binder stays below the LCA.
              let bodyClosed := body.abstract #[fvar]
              let cPrime := Expr.forallE e.bindingName! dom bodyClosed e.bindingInfo!
              finalize κ cPrime acc nB nG nOr
    else
      finalize κ e acc nB nG nOr

  finalize (κ : KVar) (cPrime : Expr) (acc : List (FVarId × Name))
      (nB nG nOr : Nat) : KM ScopedSolPres := do
    let sol0 ← exprSol1Pres κ cPrime
    -- substitute each prefix fvar → synthetic κ-param fvar (cf. Strip.lean:142-147)
    let sol := acc.foldl
      (fun s (fvarId, paramName) =>
        s.replaceFVar (.fvar fvarId) (.fvar (FVarId.mk paramName)))
      sol0
    return { sol := sol, nBinders := nB, nGuards := nG, nOr := nOr }
