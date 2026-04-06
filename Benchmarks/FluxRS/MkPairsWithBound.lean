import LeanFixpoint

def pairQualifiers : List Qualifier := [
  q{ Le(a : int, b : int) | a ≤ b },
  q{ GeZero(v : int) | v ≥ 0 },
  q{ SumBound(a : int, b : int, c : int) | a + b ≤ c + 10 }
]

-- Merged k0/k1/k2 into single 5-param κ tracking (i, res, px, py, a₀)
def MkPairsSimple :=
  ∃ k0 : Int → Int → Int → Int → Int → Prop,
  ∀ (a₀ : Int),
    -- Init: i=0, res=0, px=10, py=a₀
    (∀ (z₀ : Int), z₀ = 0 →
     ∀ (z₁ : Int), z₁ = 0 →
     ∀ (px₀ : Int), px₀ = 10 →
     ∀ (py₀ : Int), py₀ = a₀ →
     k0 z₀ z₁ px₀ py₀ a₀) ∧
    -- Loop body
    (∀ (i₀ : Int), ∀ (res₀ : Int), ∀ (px : Int), ∀ (py : Int),
      k0 i₀ res₀ px py a₀ →
        -- Exit: px + py ≤ a₀ + 10
        ((a₀ ≤ i₀) →
          px + py ≤ a₀ + 10) ∧
        -- Continue: step i, res, rebuild pair
        ((i₀ < a₀) →
          ∀ (i₁ : Int), i₁ = i₀ + 1 →
          ∀ (res₁ : Int), res₁ = res₀ + 1 →
          ∀ (px₁ : Int), px₁ = i₁ + 10 →
          ∀ (py₁ : Int), py₁ = a₀ - i₁ →
          k0 i₁ res₁ px₁ py₁ a₀))

theorem mkPairsProof : MkPairsSimple := by
  solve_fixpoint with pairQualifiers

