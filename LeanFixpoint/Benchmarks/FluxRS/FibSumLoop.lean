
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


@[simp]
def k0 (i : Int) (total : Int) (n : Int) : Prop :=
  0 <= i /\ i <= n /\ total = fib_spec_sum i

def FibSumLoop_proof : FibSumLoop := by
  unfold FibSumLoop
  exists k0
  simp
  intros
  and_intros
  . grind
  . unfold fib_spec_sum; grind
  . intros <;> and_intros
    . intros; grind
    . intros <;> and_intros
      . grind
      . grind
      . unfold fib_spec_sum; grind

