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
  Elaborate a refinement expression to a Lean `Expr`.

  - Variables are looked up in `env`
  - Integer literals become `Int` values
  - Arithmetic becomes `HAdd.hAdd`, `HSub.hSub`, etc.
  - Comparisons become `LE.le`, `Eq`, etc. (these are `Prop`-valued)
  - Boolean connectives become `And`, `Or`, `Not`
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
      | .mod => mkAppM ``HMod.hMod #[le, re]
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
      /-
      Here, we can have cases where either we have an uninterpreted functions or k-var
      We need to add the case for uninterpreted functions
      -/
      let fExpr     ← lookupVar env f
      let argExprs  ← args.mapM (RExpr.toExpr env)
      return mkAppN fExpr argExprs.toArray

/--
  Elaborate a predicate to a Lean `Expr` (of type `Prop`).

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
  Convert a solved `Pred` with a set of free params
  into a closed function `fun (z₁ : Int, … , zₙ : Int) => ...` witness expression.
-/
def solToWitnessExpr (sol : Pred) (params : List Name) : MetaM Expr := do
  let rec go (env : VarMap) (fvars : Array Expr) : List Name → MetaM Expr
    | [] => do
      let body ← sol.toExpr env
      mkLambdaFVars fvars body
    | n :: rest =>
      withLocalDeclD n (mkConst ``Int) fun fvar => do
        go (env.insert n fvar) (fvars.push fvar) rest
  go {} #[] params
