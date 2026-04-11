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
  - **Horn constraints** (`Constraint`) — the constraint language for type checking
  - **κ-variables** (`KVar`) — unknown predicates to be solved by the constraint solver

  ## Key Types

  | Type | Role |
  |------|------|
  | `Pred` | Predicates: Native Lean4 `expr`, `κ(args)`, `p₁ ∧ p₂`|
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
  - Conjunction of predicates

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
  fvarId  : FVarId    -- actual FVarId from peeling ∃
deriving BEq, Hashable, Repr, Inhabited

instance : Hashable KVar where
  hash k := hash k.name

-- Constraints c
inductive Constraint where
  -- `p`
  | pred : Expr → Constraint
  -- `c₁ ∧ c₂`
  | conj : Constraint → Constraint → Constraint
  -- `∀ x : b. p ⇒ c`
  | imp  : Var → Expr → Expr → Constraint → Constraint
  -- note: base type `b` is using `Expr` as well
deriving Repr, Inhabited

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

/-
  `Assignment` models a solution `σ` mapping κ-variables to predicates.
  Each entry is `(κ, (params, body))` where `body` is the predicate
  solution with free variables from `params`.
-/
abbrev Assignment := List (KVar × (List Var × Expr))

-- `{x: b | p}` — a single binding assumption in the environment
structure Assumption where
  var  : Var
  ty   : BaseTy
  pred : Expr
deriving Repr

-- CHECK THIS CAREFULLY
abbrev Assumptions := List Assumption
