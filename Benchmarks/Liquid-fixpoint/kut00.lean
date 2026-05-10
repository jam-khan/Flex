import LeanFixpoint


def kut00Prop : Prop :=
  ∃ κ1 : Int → Prop,
    (∀ x : Int, x = 5 →
      ∀ y : Int, y = x →
        ∀ v : Int, v = x + y → κ1 v)
    ∧ (∀ z : Int, κ1 z → 99 < 105)

theorem kut00Proof : kut00Prop := by
  solve_fixpoint
