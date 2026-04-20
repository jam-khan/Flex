import Mathlib.Data.Finset.Basic
import LeanFixpoint

def lhSetProp : Prop :=
  ∀ xs : Finset Int, True →
    (∀ _x : Int, xs = ∅ → xs = ∅)
    ∧ (∀ a0 : Int, True → ∀ a1 : Finset Int, True →
        ∀ _x : Int, xs = {a0} ∪ a1 → xs ≠ ∅)

theorem lhSetProof : lhSetProp := by
    unfold lhSetProp
    intro xs ht
    constructor
    · grind
    · intros
      simp_all; grind
