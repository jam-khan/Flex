import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__Clear
-- import LeanProofs.Tactics.Tactics
import Flex
open Classical

namespace F

@[simp]
abbrev clear_inv : Int → OVec (ASeq Int Int) → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → Prop :=
  fun idx curr _ _ _ _ _ orig =>
    idx ≤ curr.length ∧
    0 < svec_len curr ∧
    svec_len curr = svec_len orig ∧
    ∀ x : Nat, 0 ≤ x ∧ x < idx → curr[x]! = .nil


theorem zero_elem_zero_sum (l : List Nat) : (∀ x ∈ l, x = 0) → l.sum = 0 := by
  induction l with
  | nil => grind
  | cons h t ih =>
    intro h ; simp
    and_intros
    · apply_assumption
      simp
    · grind

theorem empty_total_sum (v : OVec (ASeq Int Int)) (i : Int) (h1 : ∀ x : Nat, 0 ≤ x ∧ x < i → v[x]! = List.nil) (h2 : i = svec_len v) : (v.map List.length).sum = 0 := by
  apply zero_elem_zero_sum
  intros x xelem
  rcases (List.mem_iff_getElem.mp xelem) with ⟨x, h, foo⟩
  rw [List.getElem_map] at foo
  rw [←foo]
  simp at h1
  have : v[x]!.length = 0 := by grind
  grind

attribute [grind .] List.eq_replicate_iff List.mem_iff_getElem in
def BucketMapImpl__0__Clear_proof : BucketMapImpl__0__Clear := by
  unfold BucketMapImpl__0__Clear
  exists clear_inv ; unfold clear_inv at *
  elim_leaves
  · split_hyp_ands
    apply Eq.symm ; simp
    apply empty_total_sum
    assumption
    grind only [= svec_len.eq_1]
  · unfold bucket_map_unique_keys alist_aseq_unique_keys at *
    intros b belem
    have : b = List.nil := by
      rw [List.mem_iff_getElem] at belem
      grind only [= svec_len.eq_1, = getElem!_pos]
    simp_all

end F
