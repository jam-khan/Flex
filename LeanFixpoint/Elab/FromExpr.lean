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
  | eq   : Expr → Expr → PropAST   -- lhs = rhs (sub-exprs, for kvar-arg analysis)
  | le   : Expr → Expr → PropAST
  | nonNeg : Expr → PropAST
  | forall_ : Name → Expr → PropAST → PropAST
  | exists_ : Name → Expr → PropAST → PropAST
  | app  : Expr → Array Expr → PropAST  -- κ(ν₁, ..., νₙ)
  | atom : Expr → PropAST               -- opaque Prop, pass through as-is
  deriving Repr

partial def toPropASTWithTracking
    (fvarsRef : IO.Ref FVarMap)
    (kvarsRef : IO.Ref KVarSet)
    (e : Expr) : MetaM PropAST := do
  let orig := e  -- keep original before whnf for passthrough
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
      return .eq lhs rhs  -- keep .eq for neg/imp pattern matching
    else if e.isAppOfArity ``LE.le 4 then
      return .atom orig
    else if e.isAppOfArity ``Int.NonNeg 1 then
      return .atom orig
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

    -- κ(ν₁, ..., vₙ) (predicate variable applied to multiple args)
    else if e.getAppFn.isFVar then
      let fn := e.getAppFn
      let args := e.getAppArgs
      return .app fn args
    else
      throwError "toPropAST: unhandled: {e}"

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
  | .imp guard body =>
      let guardPred ← toPred fvars kvars guard
      let bodyC ← toConstraint fvars kvars body
      return .imp `_anon .int guardPred bodyC
  | other =>
    return .pred (← toPred fvars kvars other)

  where
    -- Replace fvars in `e` with stable name-keyed fvars.
    -- Each fvar whose id appears in `fvars` is replaced by a synthetic fvar
    -- whose FVarId.name == the variable name. This makes the expression
    -- independent of the withLocalDecl scope, and Pred.toExpr can resolve
    -- these stable fvars by name from VarMap.
    normalizeFVars (fvars : FVarMap) (e : Expr) : MetaM Expr := do
      return e.replace fun sub =>
        if sub.isFVar then
          let id := sub.fvarId!
          if let some name := fvars.get? id then
            -- Create a stable fvar whose FVarId is the name itself
            some (mkFVar { name := name })
          else none
        else none

    toPred (fvars : FVarMap) (kvars : KVarSet)
    (ast : PropAST) : MetaM Pred := do
    match ast with
    | .tt   => return .tru
    | .ff   => return .fls
    | .atom e =>
        return .rexpr (← normalizeFVars fvars e)   -- re-ground fvars before storing
    | .eq lhs rhs =>
        let lhsName : Option Name :=
          if lhs.isFVar then fvars.get? lhs.fvarId! else none
        let rhsName : Option Name :=
          if rhs.isFVar then fvars.get? rhs.fvarId! else none
        match lhsName, rhsName with
        | some pi, some ai => return .eqVars pi ai   -- var = var
        | some pi, none    =>                         -- var = expr
            let rhsN ← normalizeFVars fvars rhs
            return .eqExpr pi rhsN                   -- resolved at toExpr time
        | _, _ =>
            -- lhs is compound: normalize the whole original expression as rexpr
            return .rexpr (← normalizeFVars fvars (← mkAppM ``Eq #[lhs, rhs]))
    | .le _ _ | .nonNeg _ =>
        -- these should be .atom now; shouldn't reach here
        throwError "toPred: unexpected .le/.nonNeg (should be .atom)"
    | .app fn args =>
        let fnId := fn.fvarId!
        if kvars.contains fnId then
          let κName    := (Std.HashMap.get? fvars fn.fvarId!).getD `unknown
          let argExprs ← args.toList.mapM fun arg => normalizeFVars fvars arg
          let canonParams := (List.range argExprs.length).map fun i => Name.mkStr1 s!"z{i}"
          let kvar : KVar := { name := κName, params := canonParams }
          return .kapp kvar argExprs
        else
          return .rexpr (mkAppN fn args)
    | .and l r =>
        return .conj (← toPred fvars kvars l) (← toPred fvars kvars r)
    | .neg p =>
        match p with
          | .atom e => return .rexpr (← mkAppM ``Not #[e])
          | .le lhs rhs => return .rexpr (← mkAppM ``LT.lt #[rhs, lhs])
          | .eq lhs rhs =>
              let eq ← mkAppM ``Eq #[lhs, rhs]
              return .rexpr (← mkAppM ``Not #[eq])
          | _ => throwError "toPred: unsupported negation pattern: {repr p}"
    | .imp (.atom e) .ff => return .rexpr (← mkAppM ``Not #[e])
    | .imp (.eq lhs rhs) .ff => do
        let eq ← mkAppM ``Eq #[lhs, rhs]
        return .rexpr (← mkAppM ``Not #[eq])
    | .imp (.le lhs rhs) .ff =>
        return .rexpr (← mkAppM ``LT.lt #[rhs, lhs])
    | _ =>
        throwError "toPred: unhandled: {repr ast}"
