import Lean
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion

import Std.Data.DHashMap

open Lean Meta Elab Term Tactic

--Maps our AST variable names to Lean free variables (`Expr.fvar`)
abbrev VarMap := Std.HashMap Name Expr

-- Look up a variable in an `env`, throw error if not found
def lookupVar (env : VarMap) (n : Name) : MetaM Expr := do
  match env.get? n with
  | some e => return e
  | none   => throwError s!"Elab: unbound variable `{n}`"

-- `BaseTy` AST to `Lean.Expr`
def BaseTy.toExpr : BaseTy → Expr
  | .int  => mkConst ``Int
  | .bool => mkConst ``Bool

/--
  Elaborate a predicate to a Lean `Expr` (of type `Prop`).
  - `kapp`        → error (should be eliminated before elaboration)
-/
def Pred.toExpr (env : VarMap) : Pred → MetaM Expr
  | .tru => return mkConst ``True
  | .fls => return mkConst ``False
  | .rexpr e =>
    -- Resolve any stable name-keyed fvars (FVarId.name == var name) via env
    return e.replace fun sub =>
      if sub.isFVar then
        let n := sub.fvarId!.name
        env.get? n
      else none
  | .eqVars pi ai => do
    let lhs ← lookupVar env pi
    let rhs ← lookupVar env ai
    let lhsTy ← inferType lhs
    mkAppOptM ``Eq #[lhsTy, lhs, rhs]
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
  | .eqExpr v e => do
    let lhs ← lookupVar env v
    let rhs := e.replace fun sub => if sub.isFVar then env.get? sub.fvarId!.name else none
    mkAppOptM ``Eq #[← inferType lhs, lhs, rhs]
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
  Convert a solved `Pred` with a set of free params
  into a closed function `fun (z₁ : Int, … , zₙ : Int) => ...` witness expression.
-/
def solToWitnessExpr (sol : Pred) (params : List Name) (env : VarMap := {}): MetaM Expr := do
  let rec go (env : VarMap) (fvars : Array Expr) : List Name → MetaM Expr
    | [] => do
      let body ← sol.toExpr env
      mkLambdaFVars fvars body
    | n :: rest =>
      withLocalDeclD n (mkConst ``Int) fun fvar => do
        go (env.insert n fvar) (fvars.push fvar) rest
  go env #[] params
