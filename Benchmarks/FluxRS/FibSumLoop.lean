import LeanFixpoint

@[grind]
def fib_spec_sum (n : Int) : Int :=
  if n <= 0 then 0 else  n + fib_spec_sum ( n - 1)
  termination_by n.toNat

def FibSumLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop,
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 0 n₀))) ∧
   (∀ (i₀ : Int),
    ∀ (total₀ : Int),
     ((k0 i₀ total₀ n₀)) ->
      ((¬(i₀ < n₀)) ->
       (total₀ = (fib_spec_sum n₀))) ∧
      ((i₀ < n₀) ->
       ((k0 (i₀ + 1) (total₀ + (i₀ + 1)) n₀)))
      )


@[qualif] def q1  (a b : Int) : Prop := a = b
@[qualif] def q2  (a b : Int) : Prop := a ≥ b
@[qualif] def q3  (a b : Int) : Prop := a > b
@[qualif] def q4  (a b : Int) : Prop := a ≤ b
@[qualif] def q5  (a b : Int) : Prop := a != b
@[qualif] def q6  (t i : Int) : Prop := t = fib_spec_sum i
@[qualif] def q7  (i : Int) : Prop := i ≥ 0

-- @[simp]
-- def k0 (i : Int) (total : Int) (n : Int) : Prop :=
--   0 <= i /\ i <= n /\ total = fib_spec_sum i

def FibSumLoop_proof : FibSumLoop := by
  solve_fixpoint
