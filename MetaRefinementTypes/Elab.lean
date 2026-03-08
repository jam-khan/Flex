import Lean
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Constraint

import Std.Data.DHashMap

/-!
  # Elab.lean — Elaboration from Constraint AST to Lean.Expr

  After κ-variable elimination, constraints are κ-free.
  We elaborate them into native Lean propositions (`Lean.Expr`)
  so they can be discharged by `grind` or `omega`.

  ## Pipeline

  ```
  Constraint
  → elim
  → Constraint (κ-free)
  → constraintToExpr
  → Expr (Prop)
  ```

  ## Architecture

  The elaboration is stratified:

  1. `RExpr.toExpr`      : RExpr      → ReaderT VarMap MetaM Expr
  2. `Pred.toExpr`       : Pred       → ReaderT VarMap MetaM Expr
  3. `Constraint.toExpr` : Constraint → ReaderT VarMap MetaM Expr
  4. `checkVC`           : Constraint → MetaM Bool

  `VarMap` tracks bound variables: maps `Name → Expr` (free variables
  introduced by `∀` binders in constraints and `∃` binders in preds).
-/

open Lean Meta Elab Term Tactic

/-
  Maps our AST variable names to Lean free variables (`Expr.fvar`)

  See `Std.HashMap` at
  `https://leanprover-community.github.io/mathlib4_docs/Std/Data/HashMap/Basic.html`
-/
abbrev VarMap := Std.HashMap Name Expr

-- Look up a variable in an `env`, throw error if not found
def lookupVar (env : VarMap) (n : Name) : MetaM Expr := do
  match env.get? n with
  | some e => return e
  | none   => throwError s!"Elab: unbound variable `{n}`"

/-
  Simple type elaboration from
  `BaseTy` AST to `Lean.Expr`
-/
def BaseTy.toExpr : BaseTy → Expr
  | .int  => mkConst ``Int
  | .bool => mkConst ``Bool

/--
  Elaborate a refinement expression to a Lean `Expr`.

  - Variables are looked up in `env`
  - Integer literals become `Int` values
  - Arithmetic becomes `HAdd.hAdd`, `HSub.hSub`, etc.
  - Comparisons become `LE.le`, `Eq`, etc. (these are `Prop`-valued)
  - Boolean connectives become `And`, `Or`, `Not`

  Note: Partial as termination proof required.
-/
partial def RExpr.toExpr (env : VarMap) : RExpr → MetaM Expr
  | .var n =>
      lookupVar env n
  /-
    `integer` literal elaboration is a bit subtle.

    Lean's `Int` has two constructors `ofNat` and `negSucc`.
    So, `n: Int` needs to be elaborated to
      - (n ≥ 0)   ~> ofNat n
      - ¬(n ≥ 0)  ~> negSucc (n - 1) ≃ - ((n - 1) + 1)
  -/
  | .int n =>
    if n ≥ 0 then
      return mkApp (mkConst ``Int.ofNat) (mkNatLit n.toNat)
    else
      -- negSucc (n - 1) = -[(n - 1) + 1] = [n]
      return mkApp (mkConst ``Int.negSucc) (mkNatLit (n.natAbs - 1))
  | .bool Bool.true  =>
      return mkConst ``Bool.true
  | .bool Bool.false =>
      return mkConst ``Bool.false
  | .arith op l r => do
      let le ← l.toExpr env
      let re ← r.toExpr env
      match op with
      | .add => mkAppM ``HAdd.hAdd #[le, re]
      | .sub => mkAppM ``HSub.hSub #[le, re]
      | .mul => mkAppM ``HMul.hMul #[le, re]
      | .div => mkAppM ``HDiv.hDiv #[le, re]
  | .cmp op l r => do
      let le ← l.toExpr env
      let re ← r.toExpr env
      match op with
      | .eq => mkAppM ``Eq #[le, re]
      | .ne => do
          let eq ← mkAppM ``Eq #[le, re]
          mkAppM ``Not #[eq]
      | .lt => mkAppM ``LT.lt #[le, re]
      | .le => mkAppM ``LE.le #[le, re]
      | .gt => mkAppM ``GT.gt #[le, re]
      | .ge => mkAppM ``GE.ge #[le, re]
  | .bop op l r => do
      let le ← l.toExpr env
      let re ← r.toExpr env
      match op with
      | .and => mkAppM ``And #[le, re]
      | .or  => mkAppM ``Or #[le, re]
      | .imp => mkArrow le re
  | .not e => do
      let ee ← e.toExpr env
      mkAppM ``Not #[ee]
  | .app f args => do
      -- Note: Current examples don't use uninterpreted functions
      let fExpr     ← lookupVar env f
      let argExprs  ← args.mapM (RExpr.toExpr env)
      return mkAppN fExpr argExprs.toArray

/--
  Elaborate a predicate to a Lean `Expr` (of type `Prop`).

  - `true`        → `True`
  - `false`       → `False`
  - `rexpr r`     → elaborate `r` (already Prop-valued for cmp/bop)
  - `conj p₁ p₂`  → `And p₁ p₂`
  - `disj p₁ p₂`  → `Or p₁ p₂`
  - `exist x b p` → `∃ x : b, p`
  - `kapp`        → error (should be eliminated before elaboration)
-/
def Pred.toExpr (env : VarMap) : Pred → MetaM Expr
  | .tru => return mkConst ``True
  | .fls => return mkConst ``False
  | .rexpr r => r.toExpr env
  | .conj p₁ p₂ => do
    let e₁ ← p₁.toExpr env
    let e₂ ← p₂.toExpr env
    mkAppM ``And #[e₁, e₂]
  | .disj p₁ p₂ => do
    let e₁ ← p₁.toExpr env
    let e₂ ← p₂.toExpr env
    mkAppM ``Or #[e₁, e₂]
  | .exist x b p => do
    -- Build: ∃ x : Int, p(x)
    -- i.e., @Exists Int (fun x => p(x))
    let bTy := b.toExpr -- elaborate type b to an Expr
    /-
      `withLocalDecl` at `https://leanprover-community.github.io/mathlib4_docs/Lean/Meta/Basic.html#Lean.Meta.withLocalDecl`
        - Creates a free variable `x` with name, binder info and type
        - Adds it to context
        - Runs in `k`
        - Revert the context
      `withLocalDeclD` does same except `binderInfo` is implicitly `default`
    -/
    withLocalDeclD x bTy fun fvar => do
      -- put (x ↦ fvar) in env
      let env' := env.insert x fvar
      -- elaborate `p` in `∃ x : Int, p(x)` with updated env'
      let body ← p.toExpr env'
      -- makes lambdas fvar on elaborated `p`
      -- (fun x => p(x))
      let lam ← mkLambdaFVars #[fvar] body
      -- creates an exists with lam
      mkAppM ``Exists #[lam]
  | .kapp k _ =>
    throwError s!"Elab: κ-variable `{k.name}` not eliminated! Cannot elaborate."

/--
  Elaborate a κ-free constraint to a Lean `Expr` (of type `Prop`).

  - `pred p`      → elaborate `p`
  - `conj c₁ c₂`  → `c₁ ∧ c₂`
  - `imp x b p c` → `∀ x : b, p → c`

  The `imp` case is the key one: it introduces a universally
  quantified variable `x` into the local context, adds the
  hypothesis `p` as an implication antecedent, and recurses
  into the body `c`.
-/
def Constraint.toExpr (env : VarMap) : Constraint → MetaM Expr
  | .pred p => p.toExpr env
  | .conj c₁ c₂ => do
      let e₁ ← c₁.toExpr env
      let e₂ ← c₂.toExpr env
      mkAppM ``And #[e₁, e₂]
    -- similar to `.exist` case in `Pred.toExpr`
  | .imp x b p c => do
    -- Build: ∀ x : Int, p(x) → c(x)
    let bTy := b.toExpr
    withLocalDeclD x bTy fun fvar => do
      let env' := env.insert x fvar
      let hyp ← p.toExpr env'
      let body ← c.toExpr env'
      let imp ← mkArrow hyp body
      mkForallFVars #[fvar] imp


/--
  Try to discharge a κ-free constraint using `grind`.

  Returns `true` if `grind` closes the goal, `false` otherwise.
  Useful for testing the pipeline end-to-end.
-/
def checkVCWithGrindOmega (c : Constraint) : TermElabM Bool := do
  let prop ← c.toExpr {}
  let propTy ← inferType prop
  unless (← isDefEq propTy (mkSort .zero)) do
    throwError s!"checkVC: elaborated expression is not a Prop"
  let mvar ← mkFreshExprMVar (some prop) (kind := MetavarKind.syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      evalTactic (← `(tactic| first | grind | omega))
    return goals.isEmpty
  catch _ =>
    return Bool.false

-- Simple string representation of a constraint's elaborated form
def ppConstraintExpr (c : Constraint) : MetaM Format := do
  let e ← c.toExpr {}
  ppExpr e

/--
  `#solve_constraint c` solves for all κ-variables in constraint `c`,
  eliminates them, and tries to discharge the resulting VC with omega/grind.

  Pipeline:
  - Infer κ-variables via `c.kvars`
  - Solve each κ via `sol1` and eliminate via `elim1`
  - Elaborate the κ-free constraint to a Prop
  - Discharge with `omega` or `grind`

  Usage:
```
  #solve_constraint exConstraint
```

  Output:
```
  κ-variables: [κ2, κk]
    κ2([k]) = 0 ≤ ν ∧ k ≤ ν
    κk([k]) = ⊤
  Eliminated constraint: ...
  VC: ∀ k : Int, k < 0 → 0 ≤ 0 ∧ k ≤ 0
  ✅ VC discharged successfully
```
-/
elab "#solve_constraint " t:term : command => do
  Lean.Elab.Command.liftTermElabM do

    let elabExprC ← Lean.Elab.Term.elabTerm t (some (mkConst ``Constraint))
    let elabExprC ← instantiateMVars elabExprC

    let ty ← inferType elabExprC
    unless (← isDefEq ty (mkConst ``Constraint)) do
      throwError s!"Expected Constraint, got: {← ppExpr ty}"

    -- reflect with contained unsafe block
    let c ← try
      unsafe Lean.Meta.evalExpr Constraint (mkConst ``Constraint) elabExprC
    catch _ =>
      throwError s!"Reflection failed"

    -- everything below here is normal safe Lean
    let kvars : List KVar := c.kvars.eraseDups
    if kvars.isEmpty then
      logInfo m!"No κ-variables found, constraint is already a VC."
    else
      logInfo m!"κ-variables: {kvars.map toString}"

    let mut eliminated := c
    for κ in kvars do
      let sol := eliminated.sol1 κ
      logInfo m!"  {κ.name}({κ.params.map toString}) = {toString sol}"
      eliminated := eliminated.elim1 κ

    logInfo m!"Eliminated constraint:\n{toString eliminated}"

    let prop  ← eliminated.toExpr {}
    let fmt   ← ppExpr prop
    logInfo m!"VC: {fmt}"

    let ok ← checkVCWithGrindOmega eliminated
    if ok then
      logInfo m!"VC discharged successfully ✅"
    else
      logWarning m!"VC could not be discharged by omega or grind"
