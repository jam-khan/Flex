import LeanFixpoint
/-
  Liquid Haskell Test
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/let-binding00.smt2`

  (constraint
    (forall ((x Int) (true))
        ((let ((y 2))
            (= (* x y) (+ x x))))))
-/

def lhNonlinear : Constraint :=
  c{ ∀ x : int . true ⇒
      x * 2 == x + x }

def lhNonlinearProp : Prop :=
  ∀ x : Int, True → x * 2 = x + x

theorem lhNonlinearProof : lhNonlinearProp := by
  -- unfold lhNonlinearProp
  solve_fixpoint
