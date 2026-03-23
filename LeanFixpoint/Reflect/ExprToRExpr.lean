import Lean
import LeanFixpoint.Syntax
import LeanFixpoint.Reflect.PropAST

open Lean Elab Meta Command Tactic

abbrev FVarMap := Std.HashMap FVarId Name
abbrev KVarSet := Std.HashSet FVarId

/--
  Translate a Lean `Expr` (representing an integer expression)
  into an `RExpr` (our constraint AST for refinement expressions).

  This handles the arithmetic subset of `Expr` that appears
  inside guards and comparisons of Horn constraints:
  variables, integer literals, and arithmetic operations.

  ## How Lean encodes arithmetic

  Lean's kernel represents arithmetic uniformly via
  heterogeneous type-class operations. Each binary operation
  takes 6 arguments: `HAdd.hAdd α β γ inst lhs rhs`.
  We only care about args 4 and 5 (the actual operands).

  Numeric literals go through `OfNat.ofNat α n inst`,
  where arg 1 is the raw `Nat` literal.

  ## Variable resolution

  Free variables (`Expr.fvar`) are resolved via `fvars`,
  which maps `FVarId → Name` (populated during `toPropASTWithTracking`).
-/
partial def exprToRExpr (fvars : FVarMap) (e : Expr) : MetaM RExpr := do
  -- Free variable → look up name in fvar map
  if e.isFVar then
    let id := e.fvarId!
    let name := (Std.HashMap.get? fvars id).getD `unknown
    return .var name

  -- Raw natural literal (e.g., appears inside Nat.succ chains)
  else if let some n := e.rawNatLit? then
    return .int n

  -- HAdd.hAdd _ _ _ _ lhs rhs
  else if e.isAppOfArity ``HAdd.hAdd 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .add l r

  -- HSub.hSub _ _ _ _ lhs rhs
  else if e.isAppOfArity ``HSub.hSub 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .sub l r

  -- HMul.hMul _ _ _ _ lhs rhs
  else if e.isAppOfArity ``HMul.hMul 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .mul l r

  -- HDiv.hDiv _ _ _ _ lhs rhs
  else if e.isAppOfArity ``HDiv.hDiv 6 then
    let l ← exprToRExpr fvars (e.getArg! 4)
    let r ← exprToRExpr fvars (e.getArg! 5)
    return .arith .div l r

  -- OfNat.ofNat α n inst  (numeric literals like 0, 1, 2)
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    let nExpr := e.getArg! 1
    if let some n := nExpr.rawNatLit? then
      return .int n
    else
      throwError "exprToRExpr: non-literal OfNat: {e}"

  else
    throwError "exprToRExpr: unhandled: {e}"
