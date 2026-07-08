import Flex

def lhNonlinearProp : Prop :=
  ∀ x : Int, True → x * 2 = x + x

theorem lhNonlinearProof : lhNonlinearProp := by
  solve_fixpoint
