import LeanFixpoint

def constantProp : Prop :=
  ∀ f : Int → Int,
    ∃ κ0 : Int → Int → Prop,
      ∀ x : Int, x > 0 →
        (∀ v : Int, v = f x → κ0 v x)
        ∧ (∀ z : Int, κ0 z x → z = f x)


theorem constantProof : constantProp := by
  solve_fusion
