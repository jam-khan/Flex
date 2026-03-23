import Lean
import LeanFixpoint.Syntax
import LeanFixpoint.Reflect.PropAST

open Lean Elab Meta Command Tactic

abbrev FVarMap := Std.HashMap FVarId Name
abbrev KVarSet := Std.HashSet FVarId

/--
  Translate a Lean `Expr` (of type `Prop`) into a `PropAST`.

  This is the first pass of the reflection pipeline:
    Expr → PropAST → Constraint

  It walks the kernel representation of a proposition and
  pattern-matches on logical connectives, quantifiers, and
  arithmetic comparisons, producing a clean intermediate AST
  that downstream passes can work with.

  ## Tracking state

  - `fvarsRef` records every free variable introduced by a
    quantifier (∀ or ∃), mapping its `FVarId` to its user-facing
    `Name`. This is needed later when translating variable
    references into `RExpr` or `KVar` applications.

  - `kvarsRef` tracks which free variables correspond to
    κ-variables (i.e., those bound by existential quantifiers
    over predicate types like `Int → Prop`).

  ## Supported forms

  - Logical: `True`, `False`, `∧`, `∨`, `¬`, `→`, `↔`
  - Quantifiers: `∀ x : τ, ...` and `∃ x : τ, ...`
  - Comparisons: `=`, `≤`, `Int.NonNeg`
  - Predicate application: `κ ν` (fvar applied to one argument)

  ## Arrow vs implication

  Lean encodes both `→` (implication) and `∀` (universal) as
  `Expr.forallE`. We distinguish them:
  - If the domain is `Prop`-sorted, it's an implication (`PropAST.imp`)
  - Otherwise, it's a universal quantifier (`PropAST.forall_`)
-/
partial def toPropASTWithTracking
    (fvarsRef : IO.Ref FVarMap)
    (kvarsRef : IO.Ref KVarSet)
    (e : Expr) : MetaM PropAST := do
  let e ← whnf e
  match e with
  | .const ``True _  => return .tt
  | .const ``False _ => return .ff
  | _ =>

    -- ∧
    if let some (p, q) := e.and? then
      return .and (← toPropASTWithTracking fvarsRef kvarsRef p)
                  (← toPropASTWithTracking fvarsRef kvarsRef q)

    -- ∨
    else if e.isAppOfArity ``Or 2 then
      return .or (← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 0))
                 (← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 1))

    -- ¬
    else if let some p := e.not? then
      return .neg (← toPropASTWithTracking fvarsRef kvarsRef p)

    -- =
    else if let some (_, lhs, rhs) := e.eq? then
      return .eq lhs rhs

    -- ≤
    else if e.isAppOfArity ``LE.le 4 then
      return .le (e.getArg! 2) (e.getArg! 3)

    -- Int.NonNeg (encodes 0 ≤ e)
    else if e.isAppOfArity ``Int.NonNeg 1 then
      return .nonNeg (e.getArg! 0)

    -- ∃ x : τ, body
    -- The existential binds a κ-variable when τ is a predicate type
    else if e.isAppOfArity ``Exists 2 then
      let pred := e.getArg! 1
      match pred with
      | .lam name ty body _ =>
        let ast ← withLocalDecl name .default ty fun fvar => do
          fvarsRef.modify fun m => m.insert fvar.fvarId! name
          kvarsRef.modify fun s => s.insert fvar.fvarId!
          let body := body.instantiate1 fvar
          toPropASTWithTracking fvarsRef kvarsRef body
        return .exists_ name ty ast
      | _ => throwError "toPropAST: Exists with non-lambda: {e}"

    -- ∀ and → (both encoded as Expr.forallE)
    else if e.isForall then
      let name := e.bindingName!
      let ty   := e.bindingDomain!
      let body := e.bindingBody!

      -- Arrow: domain is Prop-sorted → treat as implication
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

      -- Dependent forall
      else
        let ast ← withLocalDecl name .default ty fun fvar => do
          fvarsRef.modify fun m => m.insert fvar.fvarId! name
          toPropASTWithTracking fvarsRef kvarsRef (body.instantiate1 fvar)
        return .forall_ name ty ast

    -- ↔ (desugar to conjunction of implications)
    else if e.isAppOfArity ``Iff 2 then
      let p ← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 0)
      let q ← toPropASTWithTracking fvarsRef kvarsRef (e.getArg! 1)
      return .and (.imp p q) (.imp q p)

    -- κ ν (predicate variable applied to argument)
    -- Recognized by: the head is an fvar (introduced by ∃)
    else if e.getAppFn.isFVar then
      let fn := e.getAppFn
      let args := e.getAppArgs
      if args.size == 1 then
        return .app fn args[0]!
      else
        throwError "toPropAST: unsupported pred app arity {args.size}: {e}"

    else
      throwError "toPropAST: unhandled: {e}"
