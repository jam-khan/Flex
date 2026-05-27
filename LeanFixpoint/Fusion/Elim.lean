import LeanFixpoint.Core
import LeanFixpoint.Fusion.Flatten
import LeanFixpoint.Fusion.Graph
import LeanFixpoint.Fusion.Scope
import LeanFixpoint.Fusion.Sol1
import LeanFixpoint.Fusion.Strip

open Lean Meta

/-- `elim*(κ, sol, e)` — substitute κ with its solution throughout `e` (Fig. 11).
    Head-position κ-apps become `True`; hypothesis-position κ-apps get `substKVarInExpr`. -/
partial def exprElimStar (κ : KVar) (sol : Expr) (e : Expr) : KM Expr := do
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

/-- `elim1(κ, c)` per Cosman & Jhala 2017 §5.3 (Fig. 11).
    Returns `(σ̂_body, elim*(σ̂, c))`:
      - `σ̂_body` = `sol1(κ, scope(κ, c))`, the body of the scoped solution.
        This is what you wrap as `λx̄. σ̂_body` to assign to κ-mvar.
      - `elim*(σ̂, c)` is the constraint with κ-uses substituted away.

    Caller is responsible for assigning κ-mvar AFTER consuming the new
    constraint — never before, or `whnf` will eagerly expand `?κ` and the
    next iteration's elim1 will see no raw `?κ` to substitute. -/

def exprElim1 (κ : KVar) (e : Expr) : KM (Expr × Expr) := do
  let scoped' ← exprScope κ e
  let sol     ← exprSolScoped κ scoped'
  let newE    ← exprElimStar κ sol e
  return (sol, newE)

def exprElim (kvars : List KVar) (e : Expr) : KM (List (KVar × Expr) × Expr) := do
  let mut acc := e
  let mut sols : List (KVar × Expr) := []
  for κ in kvars do
    let (sol, acc') ← exprElim1 κ acc
    sols := sols ++ [(κ, sol)]
    acc := acc'
  return (sols, acc)
