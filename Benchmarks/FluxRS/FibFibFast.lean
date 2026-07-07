import Lean
import Flex

@[grind]
def fib_spec_fib (n : Int) : Int :=
  if n <= 1 then 1
  else fib_spec_fib (n - 1) + fib_spec_fib (n - 2)
  termination_by n.toNat

def FibFibFast := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop,
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((¬(n₀ ≤ 1)) ->
    (((k0 2 1 2 n₀))) ∧
    (∀ (i₀ : Int),
     ∀ (prev₀ : Int),
      ∀ (curr₀ : Int),
       ((k0 i₀ prev₀ curr₀ n₀)) ->
        ((¬(i₀ < n₀)) ->
         (curr₀ = (fib_spec_fib n₀))) ∧
        ((i₀ < n₀) ->
         ((k0 (i₀ + 1) curr₀ (prev₀ + curr₀) n₀)))
        )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_spec_fib n₀)))

@[qualif]
def q_le (a b : Int) : Prop := a ≤ b

@[qualif]
def q_gt_one (v : Int) : Prop := v > 1

@[qualif]
def q_eq_fib (v i : Int) : Prop := v = fib_spec_fib i

@[qualif]
def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)

theorem FibFibFast_proof : FibFibFast := by
  solve_fixpoint

