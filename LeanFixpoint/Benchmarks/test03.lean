/-
  Liquid Haskell example
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/test03.smt2`
-/

import Lean
import LeanFixpoint.Constraint
import LeanFixpoint.Elab
import LeanFixpoint.Solve
import LeanFixpoint.Qualifier
import LeanFixpoint.Syntax
import LeanFixpoint.Macros

def k0 : KVar := { name := `κ0, params := [`v] }
def lhTest1 : Constraint :=
  c{  [∀ x : int . x > 0 ⇒
        ∀ v : int . v == x ⇒ k0(v)]
    ∧ [∀ y : int . k0(y) ⇒
        ∀ v : int . v == y + 1 ⇒ k0(v)]
    ∧ [∀ z : int . k0(z) ⇒ z > 0] }

#solve_constraint_full lhTest1 with [{ pred := r{ 0 < v } }]
