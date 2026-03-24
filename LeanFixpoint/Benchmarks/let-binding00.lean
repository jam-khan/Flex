/-
  Liquid Haskell Test
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/let-binding00.smt2`
-/
import LeanFixpoint.Tactic.Command

def lhNonlinear : Constraint :=
  c{ ∀ x : int . true ⇒
      x * 2 == x + x }

#solve_constraint lhNonlinear

-- Below fail

-- def lhNonlinear2 : Constraint :=
--   c{ ∀ x : int . 0 ≤ x ⇒
--       ∀ y : int . 0 ≤ y ⇒
--         0 ≤ x * y }

-- def lhNonlinear3 : Constraint :=
--   c{ ∀ x : int . true ⇒
--       0 ≤ x * x }

-- #solve_constraint lhNonlinear2
-- #solve_constraint lhNonlinear3
