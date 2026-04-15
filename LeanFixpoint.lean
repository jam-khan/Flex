/-
  Core implementation, includes fusion algorithm
  and types for κ-variables, along with pretty printing.
-/
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Fusion

/-
  Elaboration helpers for peeling existentials
  and building witness expressions.
-/
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr

/-
  Meta-programming related code, including
  tactics, commands, and monadic code written
  in MetaM. `SolveFusion` is the main tactic to discharge
  verification conditions.
-/
import LeanFixpoint.Tactic.Command
-- import LeanFixpoint.Tactic.Grind        -- TODO: update for Expr passthrough
-- import LeanFixpoint.Tactic.SolveFixpoint -- TODO: update for Expr passthrough
import LeanFixpoint.Tactic.Tactics
import LeanFixpoint.Tactic.Utils
import LeanFixpoint.Tactic.SolveFusion

/-
  Predicate Abstraction related code,
  includes the Qualifier AST and the
  Solve method.
-/
-- import LeanFixpoint.Solve.Qualifier
-- import LeanFixpoint.Solve.Solver
-- import LeanFixpoint.Solve.Weakening
-- import LeanFixpoint.Solve.Fixpoint

/-
  Utils
-/
import LeanFixpoint.Monad
