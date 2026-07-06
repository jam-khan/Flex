import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__MoveElementsFromList
import LeanFixpoint
open Classical

namespace F

theorem absorb_app (v : OVec (ASeq Int Int))
  : bucket_map_absorb_bucket v (a ++ b) = bucket_map_absorb_bucket (bucket_map_absorb_bucket v a) b := by
  revert b v
  induction a
  case nil => simp
  case cons hd tl ih =>
    grind

def moveelementsfromlist_inv :
  ASeq Int Int → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → Int → Int → Int → Int → Prop → OVec (ASeq Int Int) → ASeq Int Int → Prop :=
    fun tl ne num denom ml sat slots ne_orig num_orig denom_orig ml_orig sat_orig slots_orig l_orig =>
      num = num_orig ∧ denom = denom_orig ∧ ml = ml_orig ∧ sat = sat_orig ∧
      ne ≥ ne_orig ∧ alist_aseq_len tl ≤ alist_aseq_len l_orig ∧ ne + alist_aseq_len tl ≤ ne_orig + alist_aseq_len l_orig ∧
      ∃ pref, pref ++ tl = l_orig ∧ slots = bucket_map_absorb_bucket slots_orig pref

attribute [grind .] BucketMapFraction.ext

def BucketMapImpl__0__MoveElementsFromList_proof : BucketMapImpl__0__MoveElementsFromList := by
  unfold BucketMapImpl__0__MoveElementsFromList
  exists moveelementsfromlist_inv ; unfold moveelementsfromlist_inv at *
  zap
  · exists .nil
  · rename_i ls1 invholds k t l0 ls1eq _ newslf _ _ _ _ _ _ _ _ _ _ _ nslotseq
    split_hyps
    rename_i pref peq aslotseq
    rw [ls1eq] at peq ; exists pref ++ [(k, t)]
    and_intros
    simp at peq ; grind only [usr List.append_assoc, = List.cons_append]
    rw [nslotseq, absorb_app, aslotseq]
    grind only [= bucket_map_absorb_bucket.eq_2, = bucket_map_absorb_bucket.eq_1, insert]
end F
