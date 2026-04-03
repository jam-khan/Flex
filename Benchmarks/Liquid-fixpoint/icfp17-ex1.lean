import LeanFixpoint
/-
(fixpoint "--eliminate=horn")

(var $k (Int))

(constraint
  (and
    (forall ((x Int) ((>= x 0)))
      (and
        (forall ((v Int) ((= v (- x 1))))
          ($k v))
        (forall ((y Int) ($k y))
          (forall ((v Int) ((= v (+ y 1))))
            ((>= v 0))))))))
-/

def lhHornProp : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ v : Int, v = x - 1 → κ v)
      ∧ (∀ y : Int, κ y → ∀ v : Int, v = y + 1 → 0 ≤ v)

theorem lhHornProof : lhHornProp := by
  solve_fixpoint
