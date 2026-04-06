import LeanFixpoint

@[ext]
structure FibBozo  where
  mkFibBozo₀ ::
    x : Int
    y : Prop

def FibTestBozo :=
  ∀ (b₀ : FibBozo),
    [Decidable (FibBozo.y b₀)] →
    ((FibBozo.x b₀) ≥ 0) →
    (¬(FibBozo.y b₀)) →
    (((FibBozo.x b₀) + 20) = (if (FibBozo.y b₀) then ((FibBozo.x b₀) + 10) else ((FibBozo.x b₀) + 20)))

def FibTestBozo_proof : FibTestBozo := by
  solve_fixpoint
