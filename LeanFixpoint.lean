/-
  Core implementation, includes fusion algorithm
  and the AST for constraint manipulation, along
  with custom Macros and pretty printing.
-/
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Core.Subst

/-
  Elaboration to and from Lean `Expr`
-/
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr

/-
  Meta-programming related code, including
  tactics, commands, and monadic code written
  in MetaM. `SolveFixpoint` is tactic to discharge
  verification conditions.
-/
import LeanFixpoint.Tactic.Command
import LeanFixpoint.Tactic.Grind
import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Tactics
import LeanFixpoint.Tactic.Utils

/-
  Predicate Abstraction related code,
  includes the Qualifier AST and the
  Solve method.
-/
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Solve.Solver
