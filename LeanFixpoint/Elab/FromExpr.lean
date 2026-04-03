import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Solve.Solver
import LeanFixpoint.Solve.Qualifier

open Lean Elab Meta Command Tactic

-- Maps fvar ids to names (for κx, κy, x, n, etc.)
abbrev FVarMap := Std.HashMap FVarId Name
-- Tracking set of `kappa` variables from `Prop` existentials
abbrev KVarSet := Std.HashSet FVarId

inductive PropAST
  | tt   : PropAST
  | ff   : PropAST
  | and  : PropAST → PropAST → PropAST
  | or   : PropAST → PropAST → PropAST
  | imp  : PropAST → PropAST → PropAST
  | neg  : PropAST → PropAST
  | eq   : Expr → Expr → PropAST
  | le   : Expr → Expr → PropAST
  | nonNeg : Expr → PropAST
  | forall_ : Name → Expr → PropAST → PropAST
  | exists_ : Name → Expr → PropAST → PropAST
  | app  : Expr → Expr → PropAST           -- κ ν  (predicate variable applied to arg)
  deriving Repr

partial def toPropASTWithTracking
    (fvarsRef : IO.Ref FVarMap)
    (kvarsRef : IO.Ref KVarSet)
    (e : Expr) : MetaM PropAST := do
  let e ← whnf e
  match e with
  | .const ``True _  => return .tt
  | .const ``False _ => return .ff
  | _ =>
    if let some (p, q) := e.and? then
      return .and (← toPropASTWithTracking fvarsRef kvarsRef p)
                  (← toPropASTWithTracking fvarsRef kvarsRef q)
    else if e.isAppOfArity ``Or 2 then
      return .or (← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 0))
                 (← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 1))
    else if let some p := e.not? then
      return .neg (← toPropASTWithTracking fvarsRef kvarsRef p)
    else if let some (_, lhs, rhs) := e.eq? then
      return .eq lhs rhs
    else if e.isAppOfArity ``LE.le 4 then
      return .le (e.getArg! 2) (e.getArg! 3)
    else if e.isAppOfArity ``Int.NonNeg 1 then
      return .nonNeg (e.getArg! 0)
    -- ∃ κ : Int → Prop, body
    else if e.isAppOfArity ``Exists 2 then
      let pred := e.getArg! 1
      match pred with
      | .lam name ty body _ =>
        let ast ← withLocalDecl name .default ty fun fvar => do
          -- Record: this fvar is a κ-variable
          fvarsRef.modify fun m => Std.HashMap.insert m fvar.fvarId! name
          kvarsRef.modify fun s => Std.HashSet.insert s fvar.fvarId!
          let body := body.instantiate1 fvar
          toPropASTWithTracking fvarsRef kvarsRef body
        return .exists_ name ty ast
      | _ => throwError "toPropAST: Exists with non-lambda: {e}"

    -- ∀ and →
    else if e.isForall then
      let name := e.bindingName!
      let ty   := e.bindingDomain!
      let body := e.bindingBody!
      if e.isArrow then
        let pSort ← inferType ty >>= whnf
        if pSort.isProp then
          let p ← toPropASTWithTracking fvarsRef kvarsRef ty
          let q ← withLocalDecl name .default ty fun fvar => do
            fvarsRef.modify fun m => m.insert fvar.fvarId! name
            toPropASTWithTracking fvarsRef kvarsRef (body.instantiate1 fvar)
          return .imp p q
        else
          let ast ← withLocalDecl name .default ty fun fvar => do
            fvarsRef.modify fun m => m.insert fvar.fvarId! name
            toPropASTWithTracking fvarsRef kvarsRef (body.instantiate1 fvar)
          return .forall_ name ty ast
      else
        let ast ← withLocalDecl name .default ty fun fvar => do
          fvarsRef.modify fun m => m.insert fvar.fvarId! name
          toPropASTWithTracking fvarsRef kvarsRef (body.instantiate1 fvar)
        return .forall_ name ty ast

    else if e.isAppOfArity ``Iff 2 then
      let p ← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 0)
      let q ← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 1)
      return .and (.imp p q) (.imp q p)

    -- κ ν  (predicate variable applied to arg)
    else if e.getAppFn.isFVar then
      let fn := e.getAppFn
      let args := e.getAppArgs
      if args.size == 1 then
        return .app fn args[0]!
      else
        throwError "toPropAST: unsupported pred app arity {args.size}: {e}"
    else
      throwError "toPropAST: unhandled: {e}"

partial def exprToRExpr (fvars : FVarMap) (e : Expr) : MetaM RExpr := do
  -- checks whether given `e` is a `fvar`
  if e.isFVar then
    let id := e.fvarId! -- get id
    let name := (Std.HashMap.get? fvars id).getD `unknown
    return .var name
  -- natural/int literal
  else if let some n := e.rawNatLit? then
    return .int n

  -- HAdd.hAdd α β γ inst lhs rhs
  else if e.isAppOfArity ``HAdd.hAdd 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .add l r

  -- HSub.hSub α β γ inst lhs rhs
  else if e.isAppOfArity ``HSub.hSub 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .sub l r

  -- HMul.hMul α β γ inst lhs rhs
  -- represents `lhs * rhs`
  else if e.isAppOfArity ``HMul.hMul 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .mul l r

  -- HDiv.hDiv α β γ inst lhs rhs
  -- represents `lhs / rhs`
  else if e.isAppOfArity ``HDiv.hDiv 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .div l r

  -- HMod.hMov α β γ inst lhs rhs
  else if e.isAppOfArity ``HMod.hMod 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .mod l r

  -- OfNat.ofNat α n inst
  -- represents numeric literals like `0`, `1`, `2`
  -- 3 args: [0]=target type [1]=raw Nat literal [2]=instance
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    let nExpr := e.getArg! 1
    if let some n := nExpr.rawNatLit? then
      return .int n
    else
      throwError "exprToRExpr: non-literal OfNat: {e}"

  else
    throwError "exprToRExpr: unhandled: {e}"

partial def toConstraint (fvars : FVarMap) (kvars : KVarSet)
    (ast : PropAST) : MetaM Constraint := do
  match ast with
  | .and l r =>
    return .conj (← toConstraint fvars kvars l) (← toConstraint fvars kvars r)
  | .exists_ _ _ty body =>
    toConstraint fvars kvars body
  | .forall_ name _ty (.imp guard body) =>
      let guardPred ← toPred fvars kvars guard
      let bodyC ← toConstraint fvars kvars body
      return .imp name .int guardPred bodyC
  | .forall_ name _ty body =>
    let bodyC ← toConstraint fvars kvars body
    return .imp name .int .tru bodyC
  | other =>
    return .pred (← toPred fvars kvars other)

  where toPred (fvars : FVarMap) (kvars : KVarSet)
    (ast : PropAST) : MetaM Pred := do
    match ast with
    | .tt => return .tru
    | .ff => return .fls
    | .eq lhs rhs =>
        return .rexpr (.cmp .eq (← exprToRExpr fvars lhs) (← exprToRExpr fvars rhs))
    | .le lhs rhs =>
        return .rexpr (.cmp .le (← exprToRExpr fvars lhs) (← exprToRExpr fvars rhs))
    | .app fn arg =>
        let fnId := fn.fvarId!
        -- We need to check whether it is a kvar or not
        if kvars.contains fnId then
          let κName   := (Std.HashMap.get? fvars fn.fvarId!).getD `unknown
          let argName := (Std.HashMap.get? fvars arg.fvarId!).getD `unknown
          let kvar : KVar := { name := κName, params := [`z] }  -- canonical param
          return .kapp kvar [argName]
        else
          throwError "toPred: uninterpreted predicate (not a κ-variable) -"
    | .and l r  =>
        return .conj (← toPred fvars kvars l) (← toPred fvars kvars r)
    | .nonNeg arg =>
        return .rexpr (.cmp .le (.int 0) (← exprToRExpr fvars arg))
    | .neg _p   =>
        throwError "toPred: negation not yet supported"
    | _ =>
        throwError "toPred: unhandled: {repr ast}"
