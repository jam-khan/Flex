import Lean

open Lean List

abbrev Var := Name

/-!
  # Types.lean — Core types for Refinement Type Constraint Solving

  Based on *Local Refinement Typing* (Cosman & Jhala, POPL 2017).

  ## Expr-Direct Design

  The fusion algorithm operates directly on native `Lean.Expr` values.
  No intermediate constraint AST — predicates, conjunctions, and
  implications are all `Expr` patterns (`And`, `forallE`, leaf).

  ## Key Types

  | Type | Role |
  |------|------|
  | `KVar` | Unknown predicate variables (κ) with parameter lists |
  | `Assignment` | Solution mapping: κ → (params, solution Expr) |
-/

-- κ(x₁, ..., xₙ)
structure KVar where
  name       : Name       -- κ
  params     : List Name  -- x₁, ..., xₙ (canonical param names)
  paramTypes : List Expr  -- types of each param (e.g. [Int, Int] or [BitVec 32])
  fvarId     : FVarId     -- actual FVarId from peeling ∃
deriving BEq, Hashable, Repr, Inhabited

instance : Hashable KVar where
  hash k := hash k.name

/-
  `Assignment` models a solution `σ` mapping κ-variables to predicates.
  Each entry is `(κ, (params, body))` where `body` is the predicate
  solution with free variables from `params`.
-/
abbrev Assignment := List (KVar × (List Var × Expr))
