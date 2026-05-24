/-
  Core implementation, includes fusion algorithm
  and types for κ-variables, along with pretty printing.
-/
import LeanFixpoint.Fusion.Types
import LeanFixpoint.Fusion.Pretty
import LeanFixpoint.Fusion.Fusion
import LeanFixpoint.Fusion.Utils
import LeanFixpoint.Fusion.Flatten
import LeanFixpoint.Fusion.Graph

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
import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Hoist
import LeanFixpoint.Tactic.Zap
import LeanFixpoint.Tactic.Internal.Utils
import LeanFixpoint.Tactic.SolveFusion
import LeanFixpoint.Tactic.Closers
import LeanFixpoint.Tactic.SplitHyps
import LeanFixpoint.Tactic.RewriteKs
import LeanFixpoint.Tactic.ZapK.ZapK
import LeanFixpoint.Tactic.Sol1

/-
  Predicate Abstraction related code,
  includes the Qualifier AST and the
  Solve method.
-/
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Solve.Instantiation
import LeanFixpoint.Solve.Weaken
import LeanFixpoint.Solve.Fixpoint

/-
  Sound Verification Condition Generation
-/
import LeanFixpoint.VCG.While.Types
import LeanFixpoint.VCG.While.Semantics

/-
  Utils
-/
import LeanFixpoint.Monad

/-
  Sound verified gen for λᵣ
-/
import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution
import LeanFixpoint.VCG.STLC.Entailment
import LeanFixpoint.VCG.STLC.Typing
import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative
import LeanFixpoint.VCG.STLC.Semantics
import LeanFixpoint.VCG.STLC.Safety
