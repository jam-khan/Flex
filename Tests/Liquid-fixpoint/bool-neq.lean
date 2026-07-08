
import Flex

def boolNeqProp : Prop :=
  (∀ x : Int, x > 0 → ∀ y : Int, y > x →
    ∀ b : Bool, ¬(b ↔ (x ≤ 0 ∨ y ≤ 0)) → b)
  ∧ (∀ x : Int, x > 0 → ∀ y : Int, y > x →
    ∀ b : Bool, ¬(b ↔ (x ≤ 0 ∨ y ≤ 0)) → b)

theorem boolNeqProof : boolNeqProp := by
  solve_fixpoint
