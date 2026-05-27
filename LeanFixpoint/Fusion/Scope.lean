import LeanFixpoint.Core
import LeanFixpoint.Fusion.Flatten
import LeanFixpoint.Fusion.Graph

open Lean Meta

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
