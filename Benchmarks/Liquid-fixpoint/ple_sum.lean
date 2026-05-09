import LeanFixpoint

@[grind, simp]
def mySum (n : Int) : Int :=
  if n ≤ 0 then 0 else n + mySum (n - 1)
termination_by n.toNat

def pleSumProp : Prop :=
  ∀ x : Int, x = 5 → mySum x = 15

theorem pleSumProof : pleSumProp := by
  solve_fixpoint
