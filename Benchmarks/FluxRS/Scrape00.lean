
import LeanFixpoint

@[qualif]
def q1 (a : Int) (b : Int) (c : Int) := a = b - c

@[qualif]
def q2 (a : Int) (b : Int) := a ≤ b

@[qualif]
def q3 (v : Int) := v ≥ 0

def TestEx := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop,
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ ≤ hi₀) ->
    (lo₀ ≥ 0) ->
     (hi₀ ≥ 0) ->
      (∀ (init₀ : Int), init₀ = 0 →
        k0 lo₀ init₀ lo₀ hi₀) ∧
      (∀ (i₀ : Int),
       ∀ (res₀ : Int),
        ((k0 i₀ res₀ lo₀ hi₀)) ->
         ((hi₀ ≤ i₀) ->
          (res₀ = (hi₀ - lo₀))) ∧
         ((i₀ < hi₀) ->
          ∀ (i₁ : Int), i₁ = i₀ + 1 →
          ∀ (res₁ : Int), res₁ = res₀ + 1 →
          k0 i₁ res₁ lo₀ hi₀)
         )

theorem testProof : TestEx := by
  solve_fixpoint
