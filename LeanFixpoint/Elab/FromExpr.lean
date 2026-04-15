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
