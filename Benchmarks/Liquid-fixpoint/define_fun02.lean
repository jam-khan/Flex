import Mathlib.Data.Finset.Basic
import LeanFixpoint

/-
  Liquid-fixpoint test — ground set property:
    ∀ xs : Finset ℤ,
      (xs = ∅ → xs = ∅)                             -- trivial
    ∧ (∀ a0 a1, xs = {a0} ∪ a1 → xs ≠ ∅)            -- nonempty if it has an element

  `∅` is disambiguated as `Finset Int` (the ambient `State` from LeanFixpoint
  has its own `∅` that conflicts otherwise).
-/

def lhSetProp : Prop :=
  ∀ xs : Finset Int, True →
    (∀ _x : Int, xs = (∅ : Finset Int) → xs = (∅ : Finset Int))
    ∧ (∀ a0 : Int, True → ∀ a1 : Finset Int, True →
        ∀ _x : Int, xs = {a0} ∪ a1 → xs ≠ (∅ : Finset Int))

theorem lhSetProof : lhSetProp := by
  intro xs _
  refine ⟨fun _ h => h, ?_⟩
  intro a0 _ a1 _ _x hxs
  rw [hxs, ← Finset.nonempty_iff_ne_empty]
  exact ⟨a0, by simp⟩
