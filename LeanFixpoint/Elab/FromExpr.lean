import Lean
import LeanFixpoint.Core.Types
import LeanFixpoint.Monad

open Lean Meta

partial def peelExistentials (e : Expr)
    (kvars : Std.HashMap FVarId KVar := {}) :
    MetaM (Std.HashMap FVarId KVar × Expr) := do
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
        -- here, we get no. of `→` in the `k`'s type, e.g. 2 means `Int → Int → Prop`
        let arity ← countArrows tyBind
        -- below creates parameters for `κ`
        -- based on arity, e.g. [\`z0, \`z1]
        let canonParams := (List.range arity).map fun i => Name.mkStr1 s!"z{i}"
        -- Create a custom `KVar`
        -- name of the `k`
        -- params created
        -- concrete free variable id
        let kvar : KVar := {name, params := canonParams, fvarId := fvar.fvarId! }
        let kvars' := kvars.insert fvar.fvarId! kvar
        peelExistentials (body.instantiate1 fvar) kvars'
    | _ => return (kvars, e)
  else
    return (kvars, e)
where
  countArrows (ty : Expr) : MetaM Nat := do
    let ty ← whnf ty
    if ty.isForall then return 1 + (← countArrows ty.bindingBody!)
    else return 0

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
      -- Since isArrow guarantees body doesn't reference bvar 0,
      -- we can use body directly without instantiation
      if e.isArrow then
        let bodyC ← exprToConstraint body
        return .imp name ty ty bodyC
      else
        -- dependent: ∀ (h : P), Q(h)
        withLocalDeclD name ty fun fvar => do
          let bodyC ← exprToConstraint (body.instantiate1 fvar)
          return .imp name ty ty bodyC
    else
      -- ∀ x : τ, body -- introduce x, then look for arrow inside
      withLocalDeclD name ty fun fvar => do
        let body' ← whnf (body.instantiate1 fvar)
        if body'.isForall && body'.isArrow then
          let innerDom := body'.bindingDomain!
          -- lifting required as we are in KM
          let innerSort ← (inferType innerDom >>= whnf : MetaM Expr)
          if innerSort.isProp then
            -- Combined: imp x τ hyp restC
            let restC ← exprToConstraint body'.bindingBody!
            return .imp name ty innerDom restC
          else
            -- Inner ∀ has non-Prop domain, don't combine
            let bodyC ← exprToConstraint body'
            return .imp name ty (mkConst ``True) bodyC
        else
          -- No arrow follows, just ∀ x : τ, with trivial guard
          let bodyC ← exprToConstraint body'
          return .imp name ty (mkConst ``True) bodyC
  else
    return .pred e
