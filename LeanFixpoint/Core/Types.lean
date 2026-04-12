import Lean

open Lean List

abbrev Var := Name

/-!
  # Types.lean — Core AST for Refinement Type Constraint Solving

  Based on *Local Refinement Typing* (Cosman & Jhala, POPL 2017).

  ## Expr Passthrough Design

  Refinement expressions are native `Lean.Expr` values throughout the
  entire pipeline — no custom expression AST, no translation to external
  solvers. Substitution uses `Expr.replace`, validity checking uses
  `omega`/`grind`.

  ## Key Types

  | Type | Role |
  |------|------|
  | `Constraint` | Horn clauses: `p`, `c₁ ∧ c₂`, `∀x:τ. p ⇒ c` |
  | `KVar` | Unknown predicate variables (κ) with parameter lists |
  | `FlatConstraint` | A constraint known to be in flat (non-nested) form |

  ## Relationship to the Paper

  The definitions here correspond to **Fig. 5** (Constraint Syntax) and
  **Fig. 8** (Constraint Generation) of the paper. The constraint language
  is in *Negation Normal Form* (NNF), where implications only appear
  guarded by universal quantifiers (`∀x:τ. p ⇒ c`).
-/

/-!
  ## Horn Constraints

  The constraint language from **Fig. 5** of the paper.

  ### κ-Variables (`KVar`)

  A κ-variable represents an unknown predicate to be solved.
  It has a name, a list of parameter names that scope over its solution,
  and an `FVarId` from peeling the existential quantifier.

  ### Constraints (`Constraint`)

  Constraints are the core data structure for type checking.
  Predicates and binder types are native `Lean.Expr` values.
  A constraint is either:
  - A predicate `p` (leaf `Expr`)
  - A conjunction `c₁ ∧ c₂`
  - A guarded implication `∀x:τ. p ⇒ c` (the key Horn clause form)

  ### Flat Constraints (`FlatConstraint`)

  A flat constraint has the form `∀x₁:τ₁. p₁ ⇒ ... ⇒ ∀xₙ:τₙ. pₙ ⇒ p`
  (no nested conjunctions).
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

-- `{x : τ | p}` — a single binding assumption in the environment
structure Assumption where
  var  : Var
  ty   : Expr
  pred : Expr
deriving Repr

abbrev Assumptions := List Assumption
