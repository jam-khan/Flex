import Lean
import LeanFixpoint.Constraint
import LeanFixpoint.Elab
import LeanFixpoint.Solve
import LeanFixpoint.Qualifier
import LeanFixpoint.Syntax
import LeanFixpoint.Macros
import LeanFixpoint.Tactics

/-
Current Plan for experiment:

  1. Write a Prop for Example 2.
  2. Reduce to Exp and investigate
  3. Get an elaborator from Prop (Restricted Exp)
  to Constraint
  4. Connect it to remaining `#solve_constraint`
  5. Get example working end-to-end for example 1
-/

open Lean Elab Meta Command Tactic

-- Maps fvar ids to names (for κx, κy, x, n, etc.)
abbrev FVarMap := Std.HashMap FVarId Name

-- Tracking set of `kappa` variables from `Prop` existentials
abbrev KVarSet := Std.HashSet FVarId


elab "#inspect_prop" t:term : command => do
  liftTermElabM do
    let expr ← Term.elabTerm t (some (mkSort levelZero))

    let reduced ← reduce expr
    logInfo m!"Reduced Expr:\n{reduced}"
    dbg_trace "Reduced raw: {toString reduced}"   -- raw, no pretty print

    let expr ← instantiateMVars expr
    let whnfExpr ← whnf expr
    logInfo m!"WHNF:\n{whnfExpr}"
    dbg_trace "WHNF raw: {toString whnfExpr}"     -- raw, no pretty print

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

  -- ∃ κ : Int → Prop, body
  -- Existentials bind κ-variables; we
  -- keep track of κ-variables when an existential
  -- is encountered, and continue recursing
  -- inside the body.
  | .exists_ name _ty body =>
    toConstraint fvars kvars body

  -- ∀ x : Int, (guard → body) → Constraint.imp x .int guard body
  -- standard horn clause form: ∀ x : b. p ⇒ c
  -- You computed guardPred but used .tru — use guardPred!
  | .forall_ name _ty (.imp guard body) =>
    let guardPred ← toPred fvars kvars guard
    let bodyC ← toConstraint fvars kvars body
    return .imp name .int guardPred bodyC

  -- Add the missing no-guard forall case
  | .forall_ name _ty body =>
    let bodyC ← toConstraint fvars kvars body
    return .imp name .int .tru bodyC

  -- leaf: just a predicate
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
  -- κ applied to argument: e.g. κx(v)
  -- fn is the fvar for κ, arg is the fvar for the argument
  | .app fn arg =>
    let κName   := (Std.HashMap.get? fvars fn.fvarId!).getD `unknown
    let argName := (Std.HashMap.get? fvars arg.fvarId!).getD `unknown
    let kvar : KVar := { name := κName, params := [`z] }  -- canonical param
    return .kapp kvar [argName]
  | .and l r  =>
    return .conj (← toPred fvars kvars l) (← toPred fvars kvars r)
  | .nonNeg arg =>
    return .rexpr (.cmp .le (.int 0) (← exprToRExpr fvars arg))
  | .neg _p   =>
    throwError "toPred: negation not yet supported"
  | _ => throwError "toPred: unhandled: {repr ast}"

elab "#translate_and_solve" t:term : command => do
  liftTermElabM do
    let expr ← Term.elabTerm t (some (mkSort levelZero))
    let reduced ← reduce expr

    -- Phase 1: Expr → PropAST
    let fvarsRef ← IO.mkRef ({} : FVarMap)
    let kvarsRef ← IO.mkRef ({} : KVarSet)
    let propAST ← toPropASTWithTracking fvarsRef kvarsRef reduced
    let fvarMap ← fvarsRef.get
    let kvarSet ← kvarsRef.get

    -- Phase 2: PropAST → Constraint
    let constraint ← toConstraint fvarMap kvarSet propAST
    logInfo m!"Translated Constraint:\n{toString constraint}"

    -- Phase 3: Solve
    solveAndCheckConstraint constraint

/--
  Convert a solved `Pred` into a `fun (z : Int) => ...` witness expression.
-/
def solToWitnessExpr (sol : Pred) (paramName : Name := `z) : MetaM Expr := do
  withLocalDeclD paramName (mkConst ``Int) fun zFvar => do
    let env : VarMap := ({} : VarMap).insert paramName zFvar
    let body ← sol.toExpr env
    mkLambdaFVars #[zFvar] body

elab "solve_fixpoint" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let reduced ← reduce goalType

  -- Translate Prop → PropAST → Constraint
  let fvarsRef ← IO.mkRef ({} : FVarMap)
  let kvarsRef ← IO.mkRef ({} : KVarSet)
  let propAST ← toPropASTWithTracking fvarsRef kvarsRef reduced
  let fvarMap ← fvarsRef.get
  let kvarSet ← kvarsRef.get
  let constraint ← toConstraint fvarMap kvarSet propAST

  -- Solve all κ-variables
  let kvars := constraint.kvars.eraseDups
  let mut solutions : List (Name × Pred) := []
  let mut curr := constraint
  for κ in kvars do
    let sol := curr.sol1 κ
    solutions := solutions ++ [(κ.name, sol)]
    curr := curr.elim1 κ

  for (_κName, sol) in solutions do
    let witness ← solToWitnessExpr sol
    let witnessSyn ← PrettyPrinter.delab witness
    evalTactic (← `(tactic| refine ⟨$witnessSyn, ?_⟩))

  -- Discharge the remaining VC
  evalTactic (← `(tactic| first | grind | omega))


def ex1Constraint : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

theorem ex1Proof :
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  solve_fixpoint

def ex2Constraint : Prop :=
  ∃ κx : Int → Prop, ∃ κy : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          (∀ ν : Int, ν = n → κx ν)
        ∧ (∀ ν : Int, ν = p → κy ν)
        ∧ (∀ ν : Int, κx ν → κy ν)
        ∧ (∀ y : Int, κy y →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν)


theorem ex2Proof : ex2Constraint := by
  unfold ex2Constraint
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ ν : Int, ν = n ∧ z = ν
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ p : Int, p = x + 1 ∧
    ((∃ ν : Int, ν = p ∧ z = ν) ∨ (∃ ν : Int, (∃ α : Int, α = n ∧ ν = α) ∧ z = ν))
  simp
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · assumption
  · exists x
    grind
  · intro _ x' _ _
    exists x'
    grind
  · intros _ _ _ _
    grind

#translate_and_solve ex2Constraint

def ex3Constraint : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν)

theorem ex3Proof : ex3Constraint := by
  unfold ex3Constraint
  exists fun z => ∃ ν : Int, 0 ≤ ν ∧ z = ν
  exists fun z => ∃ a : Int, (∃ ν : Int, 0 ≤ ν ∧ a = ν) ∧ ∃ ν : Int, ν = a - 1 ∧ z = ν
  exists fun z => ∃ b : Int, (∃ a : Int, (∃ ν : Int, 0 ≤ ν ∧ a = ν) ∧ ∃ ν : Int, ν = a - 1 ∧ b = ν) ∧ ∃ ν : Int, ν = b + 1 ∧ z = ν
  simp
  grind

#translate_and_solve ex3Constraint
