import Mathlib.Data.Finset.Basic
import LeanFixpoint

/-
(define_fun c0 () (Set_Set int) ((Set_empty 0)))
(define_fun c1 ((a2 int) (a3 (Set_Set int))) (Set_Set int) ((Set_cup (Set_sng a2) a3)))
(define_fun c2 ((a4 (Set_Set int))) bool ((= a4 (Set_empty 0))))

(constraint
 (forall ((xs (Set_Set int)) (true))
  (and
   (forall ((_$ int) ((= xs (Set_empty 0))))
    (tag ((= true (= xs (Set_empty 0)))) "0"))
   (forall ((a0 int) (true))
    (forall ((a1 (Set_Set int)) (true))
     (forall ((_$ int) ((= xs (Set_cup (Set_sng a0) a1))))
      (tag ((= false (= xs (Set_empty 0)))) "1")))))))
-/


def lhSetProp : Prop :=
  ∀ xs : Finset Int, True →
    (∀ _x : Int, xs = ∅ → xs = ∅)
    ∧ (∀ a0 : Int, True → ∀ a1 : Finset Int, True →
        ∀ _x : Int, xs = {a0} ∪ a1 → xs ≠ ∅)

theorem lhSetProof : lhSetProp := by
  unfold lhSetProp
  intro xs ht
  constructor
  · intro _
    simp
  · intro a0 ht' a1 ht'' _ h heq
    have hmem : a0 ∈ ({a0} : Finset Int) ∪ a1 :=
      Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have heq' : ({a0} : Finset Int) ∪ a1 = ∅ := h.symm.trans heq
    simp [heq'] at hmem
