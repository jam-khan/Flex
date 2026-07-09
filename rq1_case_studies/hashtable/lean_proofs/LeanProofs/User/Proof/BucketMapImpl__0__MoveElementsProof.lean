import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__MoveElements
import Flex
open Classical

namespace F

abbrev moveelements_inv1 :
  Int → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → OVec (ASeq Int Int) → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → OVec (ASeq Int Int) → Prop :=
    fun idx _ num denom mlf sat slots stolen _ num_orig denom_orig mlf_orig sat_orig slots_orig other_orig =>
      0 ≤ idx ∧ idx ≤ svec_len other_orig ∧
      num = num_orig ∧ denom = denom_orig ∧ mlf = mlf_orig ∧ sat = sat_orig ∧
      svec_len stolen = svec_len other_orig ∧ (∀ i: Nat, i < idx → stolen[i]! = .nil) ∧ (∀ i : Nat, i ≥ idx → stolen[i]! = other_orig[i]!) ∧
      slots = bucket_map_absorb_buckets slots_orig (other_orig.take idx.toNat)

abbrev moveelements_inv2 :
  ASeq Int Int → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → OVec (ASeq Int Int) → Int → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → OVec (ASeq Int Int) → Prop :=
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

theorem absorb_buckets_app (v : OVec (ASeq Int Int))
  : bucket_map_absorb_buckets v (b1 ++ b2) = bucket_map_absorb_buckets (bucket_map_absorb_buckets v b1) b2 := by
    fun_induction bucket_map_absorb_buckets <;> grind

attribute [grind .] BucketMapFraction.ext

set_option maxHeartbeats 300000

def BucketMapImpl__0__MoveElements_proof : BucketMapImpl__0__MoveElements := by
  unfold BucketMapImpl__0__MoveElements
  rewriteKs ; fusion
  exists moveelements_inv2, moveelements_inv1
  elim_leaves
  · grind [bucket_map_empties, List.eq_replicate_iff,List.mem_iff_get]
  · grind [Int.toNat_add, List.take_add_one, List.getElem?_eq_getElem, absorb_buckets_app]
end F
