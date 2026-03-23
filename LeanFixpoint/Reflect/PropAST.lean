import Lean

open Lean

/--
  Intermediate AST for propositions.

  Bridges Lean `Expr` and `Constraint` — isolates all Expr
  pattern matching in a single pass (`toPropASTWithTracking`),
  so downstream translation to `Constraint` is clean.
-/
inductive PropAST
  | tt       : PropAST                           -- True
  | ff       : PropAST                           -- False
  | and      : PropAST → PropAST → PropAST       -- P ∧ Q
  | or       : PropAST → PropAST → PropAST        -- P ∨ Q
  | imp      : PropAST → PropAST → PropAST       -- P → Q
  | neg      : PropAST → PropAST                 -- ¬P
  | eq       : Expr → Expr → PropAST             -- lhs = rhs
  | le       : Expr → Expr → PropAST             -- lhs ≤ rhs
  | nonNeg   : Expr → PropAST                    -- Int.NonNeg e  (i.e. 0 ≤ e)
  | forall_  : Name → Expr → PropAST → PropAST   -- ∀ x : ty, body
  | exists_  : Name → Expr → PropAST → PropAST   -- ∃ x : ty, body
  | app      : Expr → Expr → PropAST             -- κ ν  (predicate variable applied to arg)
  deriving Repr
