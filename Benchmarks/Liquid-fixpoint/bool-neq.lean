/-
(constraint
  (and
    (forall ((x Int) ((> x 0)))
      (forall ((y Int) ((> y x)))
        (forall ((b bool) ((not (<=> b (or (<= x 0) (<= y 0))))))
          (b))))
    (forall ((x Int) ((> x 0)))
      (forall ((y Int) ((> y x)))
        (forall ((b bool) ((not (<=> b (or (<= x 0) (<= y 0))))))
          (b))))))
-/
import LeanFixpoint

def boolNeqProp : Prop :=
  (∀ x : Int, x > 0 → ∀ y : Int, y > x →
    ∀ b : Bool, ¬(b ↔ (x ≤ 0 ∨ y ≤ 0)) → b)
  ∧ (∀ x : Int, x > 0 → ∀ y : Int, y > x →
    ∀ b : Bool, ¬(b ↔ (x ≤ 0 ∨ y ≤ 0)) → b)

theorem boolNeqProof : boolNeqProp := by
  solve_fixpoint
