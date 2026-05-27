import Lean
import LeanFixpoint.Core
import LeanFixpoint.Zap.Utils
import LeanFixpoint.Zap.Emit

open Lean Meta Elab


/-- Walk `goal` (the body of the proof obligation), emitting the proof
    term inline. ∀-binders become λ-abstractions; ∧-splits become
    `And.intro` with `orPath` extended on each branch; κᵢ-headed leaves
    dispatch to `emitKLeaf`; non-κ leaves become residual mvars. -/
partial def walkProof
    (kLams : List (KVar × Expr))
    (goal  : Expr)
    (binders guards : List (Name × Expr × FVarId))
    (orPath : List Bool)
    (residualOut : IO.Ref (Array MVarId)) :
    MetaM Expr := do
  -- (a) κ-headed leaf for one of our κs — check before ∀/∧ since the
  --     leaf is an application, not a binder.
  if let some (_κ, lam, args) := kHead? kLams goal then
    let lamBody := lam.beta args
    return ← emitKLeaf lamBody binders guards orPath residualOut
  -- (b) ∀ — bind, recurse, λ-wrap
  if goal.isForall then
    let dom := goal.bindingDomain!
    let name := goal.bindingName!
    let bi := goal.bindingInfo!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    return ← withLocalDecl name bi dom fun fv => do
      let body := goal.bindingBody!.instantiate1 fv
      let inner ←
        if domSort.isProp then
          walkProof kLams body binders (guards ++ [(name, dom, fv.fvarId!)])
            orPath residualOut
        else
          walkProof kLams body (binders ++ [(name, dom, fv.fvarId!)]) guards
            orPath residualOut
      mkLambdaFVars #[fv] inner
  -- (c) ∧ — split, recurse, And.intro
  if let some (l, r) := goal.and? then
    let pL ← walkProof kLams l binders guards (orPath ++ [false]) residualOut
    let pR ← walkProof kLams r binders guards (orPath ++ [true])  residualOut
    return mkAndIntro l r pL pR
  -- (d) Non-κ leaf — residual mvar
  let m ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
  residualOut.modify (·.push m.mvarId!)
  return m

-- walkPhase5 — lockstep traversal of original c against c′-witness.
--
-- Same shape as walkProof. At every position that is NOT a head-acyclic
-- κ-app, we transfer the matching position of `hCprime` (a witness of c′
-- threaded through the recursion) instead of creating a residual mvar.
partial def walkPhase5
    (kLams : List (KVar × Expr))
    (goal  : Expr)
    (hCprime : Expr)
    (binders guards : List (Name × Expr × FVarId))
    (orPath : List Bool)
    (residualOut : IO.Ref (Array MVarId)) :
    MetaM Expr := do
  -- (a) Head-acyclic-κ leaf → emitKLeaf, ignore hCprime.
  if let some (_κ, lam, args) := kHead? kLams goal then
    let lamBody := lam.beta args
    return ← emitKLeaf lamBody binders guards orPath residualOut
  -- (b) ∀ — intro fv, beta-apply hCprime to fv, recurse, λ-wrap.
  if goal.isForall then
    let dom := goal.bindingDomain!
    let name := goal.bindingName!
    let bi := goal.bindingInfo!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    return ← withLocalDecl name bi dom fun fv => do
      let body := goal.bindingBody!.instantiate1 fv
      let hCprime' := mkApp hCprime fv
      let inner ←
        if domSort.isProp then
          walkPhase5 kLams body hCprime' binders
            (guards ++ [(name, dom, fv.fvarId!)]) orPath residualOut
        else
          walkPhase5 kLams body hCprime'
            (binders ++ [(name, dom, fv.fvarId!)]) guards orPath residualOut
      mkLambdaFVars #[fv] inner
  -- (c) ∧ — project hCprime via And.left / And.right, recurse, And.intro.
  if let some (l, r) := goal.and? then
    let hL ← mkAppM ``And.left  #[hCprime]
    let hR ← mkAppM ``And.right #[hCprime]
    let pL ← walkPhase5 kLams l hL binders guards (orPath ++ [false]) residualOut
    let pR ← walkPhase5 kLams r hR binders guards (orPath ++ [true])  residualOut
    return mkAndIntro l r pL pR
  -- (d) Anything else (non-κ atom OR cyclic-κ-head app) — direct transfer.
  return hCprime
