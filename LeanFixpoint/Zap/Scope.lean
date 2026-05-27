import Lean
import LeanFixpoint.Core

open Lean Meta Elab Tactic

-- NOTE: WE NEED TO MATCH FUSION LATER

-- Preserve-And scope/sol1 for ZapK
--
-- `exprScope` / `exprSol1` in `Core/Fusion.lean` strip non-κ branches
-- of `∧` — that form is what `solve_fixpoint` is tuned for. ZapK needs
-- the FULL And-tree preserved so the goal's And ↔ sol's Or position
-- mirror holds (otherwise walkProof's orPath bits land on the wrong
-- Or branch). These local copies do exactly that.
partial def exprScopePres (κ : KVar) (e : Expr) : KM Expr := do
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
