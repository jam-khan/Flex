import LeanFixpoint
/-
(var $k0 (int)) ;; orig: $k0

(constraint
  (and
    (forall ((a0 int) ((= a0 0)))
      ($k0 a0))
    (forall ((a1 int) (true))
      (forall ((_$ int) ($k0 a1))
        (tag ((= a1 0)) "0")))
    (forall ((a2 int) (true))
      (forall ((_$ int) ((= a2 0)))
        ($k0 a2)))))
-/

def existsOddityProp : Prop :=
  ∃ κ0 : Int → Prop,
    (∀ a0 : Int, a0 = 0 → κ0 a0)
    ∧ (∀ a1 : Int, True → ∀ _x : Int, κ0 a1 → a1 = 0)
    ∧ (∀ a2 : Int, True → ∀ _x : Int, a2 = 0 → κ0 a2)

theorem existsOddityProof : existsOddityProp := by
  solve_fixpoint
