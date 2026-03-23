import Lean

open Lean List

abbrev Var    := Name
abbrev TyVar  := Name

/-!
  # Types.lean — Core AST Definitions for Refinement Type Checking

  This module defines the core abstract syntax for a refinement type system
  based on the *Local Refinement Typing* framework (Cosman & Jhala, POPL 2017).

  ## Overview

  The system supports:
  - **Base types** (`Int`, `Bool`) with logical refinements
  - **Unrefined types** (`UType`) — standard types without refinements
  - **Refined types** (`RType`) — types of the form `{x : b | r}` where `r` is a predicate
  - **Refinement expressions** (`RExpr`) — the expression language for refinements
  - **Horn constraints** (`Constraint`) — the constraint language for type checking
  - **κ-variables** (`KVar`) — unknown predicates to be solved by the constraint solver

  ## Key Types

  | Type | Role |
  |------|------|
  | `RExpr` | Refinement expressions: arithmetic, comparisons, boolean connectives |
  | `Pred` | Predicates: `true`, `false`, `κ(args)`, `p₁ ∧ p₂`, `∃x:b. p` |
  | `Constraint` | Horn clauses: `p`, `c₁ ∧ c₂`, `∀x:b. p ⇒ c` |
  | `KVar` | Unknown predicate variables with parameter lists |
  | `FlatConstraint` | A constraint known to be in flat (non-nested) form |

  ## Relationship to the Paper

  The definitions here correspond to **Fig. 5** (Constraint Syntax) and
  **Fig. 8** (Constraint Generation) of the paper. The constraint language
  is in *Negation Normal Form* (NNF), where implications only appear
  guarded by universal quantifiers (`∀x:b. p ⇒ c`).
-/

/-!
  ## Base Types

  `BaseTy` represents the ground types of the refinement language.
  Currently supports integers and booleans.
-/
inductive BaseTy where
  | int   : BaseTy
  | bool  : BaseTy
-- note: decidableEq allows us to get proof for equality
deriving BEq, Repr, Inhabited, DecidableEq

/-!
  ## Unrefined Types

  `UType` represents standard types without refinements.
  These are used as the "shape" of refined types — every refined type
  has an underlying unrefined type obtained by erasing refinements.

  Corresponds to `shape(τ)` in the paper.
-/
inductive UType where
  -- type variable `α`
  | tvar      : TyVar → UType
  -- b (`int` or `bool`)
  | base      : BaseTy → UType
  -- `x : τ → τ`, where `τ` is a `UType`
  | fn        : Var → UType → UType → UType
  -- `∀α. τ`, where `α` is a type variable
  | forallTy  : TyVar → UType → UType
deriving BEq, Repr, Inhabited, DecidableEq

/-!
  ## Refinement Expressions

  `RExpr` is the expression language for refinements.
  These appear inside refined types `{x : b | r}` and
  inside constraint predicates.

  ### Design Choice

  We use a custom deep embedding rather than `Lean.Syntax` or `Lean.Expr` because:
  - Pattern matching on `Lean.Syntax` is verbose due to sugared constructs
  - `Lean.Expr` is too abstract for direct manipulation
  - A custom AST keeps the prototype simple while still supporting
    elaboration to `Lean.Expr` (see `Elab.lean`)

  ### Expression Forms

  | Constructor | Example | Description |
  |-------------|---------|-------------|
  | `.var x` | `x` | Variable reference |
  | `.int n` | `42`, `-1` | Integer literal |
  | `.bool b` | `true`, `false` | Boolean literal |
  | `.arith op l r` | `x + 1` | Arithmetic: `+`, `-`, `*`, `/` |
  | `.cmp op l r` | `x ≤ y` | Comparison: `==`, `!=`, `<`, `≤`, `>`, `≥` |
  | `.bop op l r` | `p ∧ q` | Boolean connective: `∧`, `∨`, `→` |
  | `.not e` | `¬p` | Negation |
  | `.app f args` | `f(x, y)` | Uninterpreted function application |
-/

-- + | - | * | /
inductive ArithOp where
  | add | sub | mul | div
deriving BEq, Repr, DecidableEq

-- == | != | < | <= | > | >=
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
deriving BEq, Repr, DecidableEq

-- ∧ | ∨ | →
inductive BoolOp where
  | and | or | imp
deriving BEq, Repr, DecidableEq

-- Refinement expressions
inductive RExpr where
  -- κ
  | var   : Var → RExpr
  -- i
  | int   : Int → RExpr
  -- bool (`true` or `false`)
  | bool  : Bool → RExpr
  -- r₁ `ArithOp` r₂
  | arith : ArithOp → RExpr → RExpr → RExpr
  -- r₁ `CmpOp` r₂
  | cmp   : CmpOp → RExpr → RExpr → RExpr
  -- r₁ `BoolOp` r₂
  | bop   : BoolOp → RExpr → RExpr → RExpr
  -- `!r`
  | not   : RExpr → RExpr
  -- `κ(r₁, …, rₙ)` — uninterpreted function application
  | app   : Var → List RExpr → RExpr
deriving BEq, Repr, Inhabited

/-!
  ## Refined Types

  `RType` extends `UType` with refinement predicates.
  The key constructor is `.base x b r` representing `{x : b | r}`,
  a base type `b` refined by predicate `r` which may mention the
  binder `x`.

  ### Examples

  - `{ν : Int | 0 ≤ ν}` — non-negative integers
  - `{ν : Int | ν = x + 1}` — the integer `x + 1`
  - `x : {ν : Int | 0 ≤ ν} → {ν : Int | ν ≥ x}` — function with dependent output type
-/
inductive RType where -- Refined type `t`
  -- `α`
  | tvar     : TyVar → RType
  -- `{x : b | r}`
  | base     : Var → BaseTy → RExpr → RType
  -- `x : t → t`, note here fun input and out
  -- types can be refined type `t` unlike `Utype`
  | fn       : Var → RType → RType → RType
  -- `∀α. t`
  | forallTy : TyVar → RType → RType
deriving BEq, Repr, Inhabited

/-!
  ## Horn Constraints

  The constraint language from **Fig. 5** of the paper.

  ### κ-Variables (`KVar`)

  A κ-variable represents an unknown predicate to be solved.
  It has a name and a list of parameter names that scope over its solution.

  For example, `κ(x, y)` with `params = [x, y]` means the solution
  will be a predicate over two integer variables.

  ### Predicates (`Pred`)

  Predicates appear in both hypothesis and conclusion positions
  within constraints. They extend refinement expressions with:
  - κ-applications (`κ(y₁, ..., yₙ)`) — applying an unknown predicate
  - Existential quantification (`∃x:b. p`) — used in strongest solutions
  - Conjunction and disjunction of predicates

  ### Constraints (`Constraint`)

  Constraints are the core data structure for type checking.
  A constraint is either:
  - A predicate `p` (leaf)
  - A conjunction `c₁ ∧ c₂`
  - A guarded implication `∀x:b. p ⇒ c` (the key Horn clause form)

  The guarded implication `∀x:b. p ⇒ c` introduces variable `x` of
  base type `b`, assumes hypothesis `p`, and requires body `c`.
  This corresponds to one level of a Horn clause.

  ### Flat Constraints (`FlatConstraint`)

  A flat constraint has the form `∀x₁:b₁. p₁ ⇒ ... ⇒ ∀xₙ:bₙ. pₙ ⇒ p`
  (no nested conjunctions). The `FlatConstraint` wrapper provides a
  type-level guarantee that flattening has been applied, preventing
  accidental calls to `.head` and `.body` on non-flat constraints.

  See `Constraint.flat` in `Constraint.lean` (corresponds to `flat` in **Fig. 12**).
-/

-- κ(x₁, ..., xₙ)
structure KVar where
  name    : Name      -- κ
  params  : List Name -- x₁, ..., xₙ
deriving BEq, Hashable, Repr, Inhabited

instance : Hashable KVar where
  hash k := hash k.name

-- Predicates `p`
inductive Pred where
  -- `true`
  | tru   : Pred
  -- `false`
  | fls   : Pred
  -- refinement `r`
  | rexpr : RExpr → Pred
  -- `κ(y₁, ..., yₙ)`
  | kapp  : KVar → List Var → Pred
  -- `p₁ ∧ p₂`
  | conj  : Pred → Pred → Pred
  -- `p₁ ∨ p₂`
  | disj  : Pred → Pred → Pred
  -- `∃x:b. p`
  | exist : Var → BaseTy → Pred → Pred
deriving Repr, Inhabited

-- Constraints c
inductive Constraint where
  -- `p`
  | pred : Pred → Constraint
  -- `c₁ ∧ c₂`
  | conj : Constraint → Constraint → Constraint
  -- `∀ x : b. p ⇒ c`
  | imp  : Var → BaseTy → Pred → Constraint → Constraint
deriving Repr, Inhabited

/-!
  ## Utility Definitions
-/

-- Sugar for common refinement expressions
def RExpr.tt : RExpr := .bool true
def RExpr.ff : RExpr := .bool false
def RExpr.mkEq (l r : RExpr) : RExpr := .cmp .eq l r

/-
  Wrapper for flattened constraint.

  It helps to identify using type system
  whether a constraint has been flattened or
  not, and hence, avoiding wrong calls for
  .head and .body on Constraint
-/
structure FlatConstraint where
  val : Constraint
deriving Repr, Inhabited

-- Γ ::= `map x → t`
abbrev TyEnv := List (Var × RType)

/-
  `Assignment` models a solution `σ` mapping κ-variables to predicates.
  Each entry is `(κ, (params, body))` where `body` is the predicate
  solution with free variables from `params`.

  For example, `σ(κ) = λ(x,y). 0 ≤ x ∧ x ≤ y` is stored as
  `(κ, ([x, y], .conj (.rexpr (0 ≤ x)) (.rexpr (x ≤ y))))`.
-/
abbrev Assignment := List (KVar × (List Var × Pred))

-- `{x: b | p}` — a single binding assumption in the environment
structure Assumption where
  var  : Var
  ty   : BaseTy
  pred : Pred
deriving Repr

-- CHECK THIS CAREFULLY
abbrev Assumptions := List Assumption
