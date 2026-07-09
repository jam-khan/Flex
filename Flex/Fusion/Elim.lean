import Flex.Core
import Flex.Fusion.Flatten
import Flex.Fusion.Graph
import Flex.Fusion.Scope
import Flex.Fusion.Sol1
import Flex.Fusion.Strip

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
