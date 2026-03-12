/-
  Liquid Haskell Test
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/let-binding00.smt2`
-/
import LeanFixpoint.Constraint
import LeanFixpoint.Elab
import LeanFixpoint.Syntax
import LeanFixpoint.Macros

def lhNonlinear : Constraint :=
  c{ ∀ x : int . true ⇒
      x * 2 == x + x }

#solve_constraint lhNonlinear
