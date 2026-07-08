import Flex


@[qualif]
def Bar (v : Int) := v ≥ 0

def Test := ∃ k0 : (a0 : Int) → (a1 : Int) → Prop,
  (∀ a₀ : Int, a₀ = 0 → ∀ a₁ : Int, a₁ = 0 → k0 a₀ a₁) ∧
  (∀ (res₀ : Int),
   ∀ (i₀ : Int),
    k0 res₀ i₀ →
     (100 ≤ i₀ → 0 ≤ res₀) ∧
     ((100 > i₀) →
      ∀ res₁ : Int, res₁ = res₀ + 1 →
      ∀ i₁ : Int, i₁ = i₀ + 1 →
      k0 res₁ i₁))

theorem testProof : Test := by
  solve_fixpoint
