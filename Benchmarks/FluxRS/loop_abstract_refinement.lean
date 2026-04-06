import LeanFixpoint

def stressQualifiers : List Qualifier := [
  q{ Le(a : int, b : int) | a ≤ b },
  q{ GeZero(v : int) | v ≥ 0 },
  q{ Diff(a : int, b : int, c : int) | a == b - c }
]

-- Single 6-param cyclic κ, same ANF pattern as MkPairsSimple
def StressTest :=
  ∃ k : Int → Int → Int → Int → Int → Int → Prop,
  ∀ (lo : Int), ∀ (hi : Int), ∀ (n : Int),
    0 ≤ lo → lo ≤ hi → hi ≤ n →
    -- Init
    (∀ (acc₀ : Int), acc₀ = 0 →
     ∀ (cnt₀ : Int), cnt₀ = 0 →
     k lo acc₀ cnt₀ lo hi n) ∧
    -- Body
    (∀ (i : Int), ∀ (acc : Int), ∀ (cnt : Int),
     ∀ (lo₁ : Int), ∀ (hi₁ : Int), ∀ (n₁ : Int),
      k i acc cnt lo₁ hi₁ n₁ →
        -- Exit: bounds on acc and cnt
        ((hi₁ ≤ i) →
          0 ≤ acc ∧ acc ≤ n₁ ∧ 0 ≤ cnt) ∧
        -- Continue
        ((i < hi₁) →
          ∀ (ip : Int), ip = i + 1 →
          ∀ (ap : Int), ap = acc + 1 →
          ∀ (cp : Int), cp = cnt + 1 →
          k ip ap cp lo₁ hi₁ n₁))

theorem stressProof : StressTest := by
  solve_fixpoint with stressQualifiers
