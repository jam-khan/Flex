import LeanFixpoint

@[qualif]
def q1 (a : Int) : Prop := a ≥ 0

@[qualif]
def q2 (i : Int) (x : Int) : Prop :=
  i^2 > x → (i - 1)^2 ≤ x

def FibSqrt := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop,
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((x₀ ≠ 0) ->
    (((k0 0 x₀))) ∧
    (∀ (i₀ : Int),
     ((k0 i₀ x₀)) ->
      ((¬((i₀ * i₀) ≤ x₀)) ->
       (((i₀ - 1) ≥ 0)) ∧
       (((((i₀ - 1) * (i₀ - 1)) ≤ x₀)) ∧
       ((x₀ < (((i₀ - 1) + 1) * ((i₀ - 1) + 1))))
       )
       ) ∧
      (((i₀ * i₀) ≤ x₀) ->
       ((k0 (i₀ + 1) x₀)))
      )
    ) ∧
   ((¬(x₀ ≠ 0)) ->
    (((0 * 0) ≤ x₀)) ∧
    ((x₀ < ((0 + 1) * (0 + 1))))
    )

theorem fibsqrtproof : FibSqrt := by
  solve_fixpoint
