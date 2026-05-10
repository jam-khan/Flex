import Mathlib.Data.Set.Basic
import LeanFixpoint
/-
  Liquid-fixpoint test — list append (as sets).
  Source: Rust tests/pos/enums/list01.rs:51.

  2 acyclic κs:
    $k0 (Set Set Set)             — "output = xs1 ∪ xs2"
    $k1 (Set Set Set Int Set)     — "output = tail ∪ xs2"

  Scope: ∀ xs1, xs2 : Set Int
    • Empty case:  xs1 = ∅ ⇒ k0 xs2 xs1 xs2
    • Cons case:   xs1 = {a0} ∪ a1 ⇒
                     k1 (a1 ∪ xs2) xs1 xs2 a0 a1
                   ∧ (∀ a2, k1 a2 xs1 xs2 a0 a1 ⇒ k0 ({a0} ∪ a2) xs1 xs2)
    • Consumer:    ∀ a3, k0 a3 xs1 xs2 ⇒ a3 = xs1 ∪ xs2

  No self-loops → ACYCLIC → `solve_fusion`.
-/

def lhListAppendSet : Prop :=
  -- k1 has no κ-dependencies (sink); order it before k0 so existentials
  -- match the solver's topological elimination order.
  ∃ k1 : Set Int → Set Int → Set Int → Int → Set Int → Prop,
  ∃ k0 : Set Int → Set Int → Set Int → Prop,
    ∀ xs1 : Set Int, ∀ xs2 : Set Int,
        (xs1 = (∅ : Set Int) → k0 xs2 xs1 xs2)
      ∧ (∀ a0 : Int, ∀ a1 : Set Int,
            xs1 = {a0} ∪ a1 →
              k1 (a1 ∪ xs2) xs1 xs2 a0 a1
            ∧ (∀ a2 : Set Int, k1 a2 xs1 xs2 a0 a1 → k0 ({a0} ∪ a2) xs1 xs2))
      ∧ (∀ a3 : Set Int, k0 a3 xs1 xs2 → a3 = xs1 ∪ xs2)

theorem lhListAppendSetProof : lhListAppendSet := by
  solve_fixpoint
