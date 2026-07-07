import Flex

@[simp]
def fib_spec_twelve : Int := 12

def FibTwelve :=
 ((3 + 9) = (fib_spec_twelve))

def FibTwelve_proof : FibTwelve := by
  solve_fixpoint
