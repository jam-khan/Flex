import Lean
import LeanFixpoint

opaque fib_fib : Int -> Int := sorry

@[simp] axiom fib_base (n : Int) : n ≤ 1 → fib_fib n = 1
@[simp] axiom fib_rec (n : Int) : n > 1 → fib_fib n = fib_fib (n-1) + fib_fib (n-2)

def fibQualifiers : List Qualifier := [
  q{ GtZero(v : int) | v > 0 },
  q{ GeZero(v : int) | v ≥ 0 },
  q{ Le(a : int, b : int) | a ≤ b }
]
-- -- cyclic (cut) kvars
-- def k0 (a'₃ : Int) (a'₄ : Int) (a'₅ : Int) (a'₆ : Int) : Prop :=
--   ((a'₃ > 0) ∧ (a'₃ ≥ 0) ∧ (a'₃ ≤ a'₆))

def FibFibFast := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop,
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((n₀ > 1) ->
    (∀ (a₀ : Int), a₀ = 2 →
     ∀ (a₁ : Int), a₁ = 1 →
     ∀ (a₂ : Int), a₂ = 2 →
     k0 a₀ a₁ a₂ n₀) ∧
    (∀ (i₀ : Int),
     ∀ (prev₀ : Int),
      ∀ (curr₀ : Int),
       ((k0 i₀ prev₀ curr₀ n₀)) ->
        ((n₀ ≤ i₀) →
         (curr₀ = (fib_fib n₀))) ∧
        ((i₀ < n₀) →
         ∀ (i₁ : Int), i₁ = i₀ + 1 →
         ∀ (s₁ : Int), s₁ = prev₀ + curr₀ →
         ((k0 i₁ curr₀ s₁ n₀)))
        )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_fib n₀)))


theorem FibProof : FibFibFast := by
  solve_fixpoint with fibQualifiers
  sorry
  -- intro n₀ hn₀; constructor
  -- · -- n₀ > 1 branch
  --   intro hgt; constructor
  --   · -- Init: a₀=2, a₁=1, a₂=2 ⊢ invariant(2,1,2,n₀)
  --     intro a₀ ha₀ a₁ ha₁ a₂ ha₂; subst_vars
  --     and_intros <;> omega
  --   · -- Inductive step
  --     intro i₀ prev₀ curr₀ hk; dsimp only at hk; constructor
  --     · -- Exit: n₀ ≤ i₀ → curr₀ = fib_fib n₀
  --       -- Not provable from ordering invariant alone
  --       intro _; sorry
  --     · -- Continue: i₀ < n₀ → invariant(i₀+1, curr₀, prev₀+curr₀, n₀)
  --       intro hlt i₁ hi₁ s₁ hs₁; subst hi₁; subst hs₁; dsimp only
  --       obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hk
  --       and_intros <;> omega
  -- · -- Base: n₀ ≤ 1 → 1 = fib_fib n₀
  --   intro hle; exact (fib_base n₀ hle).symm
