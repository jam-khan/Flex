
import LeanFixpoint

@[simp]
def fib_spec_seven : Int := 7

def FibSeven :=
 (((3 + 2) + 2) = (fib_spec_seven))

def FibSeven_proof : FibSeven := by
  solve_fixpoint
  