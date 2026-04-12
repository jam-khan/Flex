import Lean
import LeanFixpoint.Core.Types
import LeanFixpoint.Monad

open Lean Meta

partial def peelExistentials (e : Expr)
    (kvars : Std.HashMap FVarId KVar := {})
    (k : Std.HashMap FVarId KVar → Expr → MetaM α) :
    MetaM α := do
  let e ← whnf e
  if e.isAppOfArity ``Exists 2 then
    let pred := e.getArg! 1
    match pred with
    | .lam name tyBind body _ =>
      -- create a fresh free variable fvar with (`name`, `tyBind`)
      -- add to the local context, so `inferType` and `whnf` can use it
      -- run the call back provided `fun fvar => do ...`
      -- reset/cleanup local context once callback returns
      --
      -- fvar gets unique `FVarId`
      withLocalDeclD name tyBind fun fvar => do
        let (arity, pTypes) ← collectArrowTypes tyBind
        let canonParams := (List.range arity).map fun i => Name.mkStr1 s!"z{i}"
        let kvar : KVar := {
          name, params := canonParams, paramTypes := pTypes, fvarId := fvar.fvarId!
        }
        peelExistentials (body.instantiate1 fvar) (kvars.insert fvar.fvarId! kvar) k
    | _ => k kvars e
  else
    k kvars e
where
  -- Collect arity and domain types from arrow type: Int → Int → Prop → (2, [Int, Int])
  collectArrowTypes (ty : Expr) : MetaM (Nat × List Expr) := do
    let ty ← whnf ty
    if ty.isForall then
      let domTy := ty.bindingDomain!
      let (n, rest) ← collectArrowTypes ty.bindingBody!
      return (1 + n, domTy :: rest)
    else return (0, [])

-- Walk Expr to build Constraint
partial def exprToConstraint (e : Expr) : KM Constraint := do
  let e ← whnf e
  -- P ∧ Q
  if let some (l, r) := e.and? then
    return .conj (← exprToConstraint l) (← exprToConstraint r)
  -- ∀ x : τ, body (where τ is NOT Prop)
  -- or P → Q (where domain IS Prop)
  else if e.isForall then
    let name    := e.bindingName!
    let ty      := e.bindingDomain!
    let body    := e.bindingBody!
    -- lifting required as we are in KM
    let domSort ← (inferType ty >>= whnf : MetaM Expr)
    if domSort.isProp then
      -- Bare arrow: P → Q
      -- No real binder variable — create a dummy fvar for the proof
      withLocalDeclD name ty fun fvar => do
        if e.isArrow then
          let bodyC ← exprToConstraint body
          return .imp name ty ty fvar bodyC
        else
          -- dependent: ∀ (h : P), Q(h)
          let bodyC ← exprToConstraint (body.instantiate1 fvar)
          return .imp name ty ty fvar bodyC
    else
      -- ∀ x : τ, body — introduce x, then look for arrow inside
      withLocalDeclD name ty fun fvar => do
        let body' ← whnf (body.instantiate1 fvar)
        if body'.isForall && body'.isArrow then
          let innerDom := body'.bindingDomain!
          -- lifting required as we are in KM
          let innerSort ← (inferType innerDom >>= whnf : MetaM Expr)
          if innerSort.isProp then
            -- Combined: imp x τ hyp restC
            let restC ← exprToConstraint body'.bindingBody!
            return .imp name ty innerDom fvar restC
          else
            -- Inner ∀ has non-Prop domain, don't combine
            let bodyC ← exprToConstraint body'
            return .imp name ty (mkConst ``True) fvar bodyC
        else
          -- No arrow follows, just ∀ x : τ, with trivial guard
          let bodyC ← exprToConstraint body'
          return .imp name ty (mkConst ``True) fvar bodyC
  else
    return .pred e
