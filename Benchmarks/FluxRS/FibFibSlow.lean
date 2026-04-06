import LeanFixpoint

noncomputable def fib_fib : Int → Int := sorry
@[simp] axiom fib_base (n : Int) : n ≤ 1 → fib_fib n = 1
@[simp] axiom fib_rec (n : Int) : n > 1 → fib_fib n = fib_fib (n-1) + fib_fib (n-2)

def FibFibSlow :=
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((¬(n₀ ≤ 1)) ->
    (((n₀ - 1) ≥ 0)) ∧
    (((fib_fib (n₀ - 1)) ≥ 0) ->
     (((n₀ - 2) ≥ 0)) ∧
     (((fib_fib (n₀ - 2)) ≥ 0) ->
      (((fib_fib (n₀ - 1)) + (fib_fib (n₀ - 2))) = (fib_fib n₀)))
     )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_fib n₀)))

def FibFibSlow_proof : FibFibSlow := by
  solve_fixpoint
