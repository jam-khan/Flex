import LeanFixpoint.Constraint
import LeanFixpoint.Elab
import LeanFixpoint.Syntax
-- import LeanFixpoint.Macros

def ex1Constraint : Prop :=
  ∃ kappa : Int → Prop,
    ∀ x : Int,
      (0 ≤ x) →
        (∀ ν : Int, ν == x - 1 → (kappa ν))
      ∧ (∀ y : Int, (kappa y) →
          ∀ ν : Int, ν == y + 1 → 0 ≤ ν )

theorem ex1ConstraintProof : ex1Constraint :=
  by sorry
