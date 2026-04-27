import LeanFixpoint
/-
  (constraint
    (forall ((x Int) (true))
        ((let ((y 2))
            (= (* x y) (+ x x))))))
-/

def lhNonlinearProp : Prop :=
  ∀ x : Int, True → x * 2 = x + x

theorem lhNonlinearProof : lhNonlinearProp := by
  solve_fixpoint
