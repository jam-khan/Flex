import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmInsert
import LeanProofs.User.Proof.Theorems
import LeanProofs.User.Proof.BucketMapImpl__0__TryResizeProof
import LeanFixpoint
open Classical
set_option linter.unusedVariables false


namespace F

set_option maxHeartbeats 1000000

-- Common setup shared by all three goals: the post-insert (pre-resize) slots `insert hm₀.slots k₀ v₀`
-- satisfy the same invariants as `hm₀.slots`, and `new_slf₀.slots` is exactly that, optionally resized.
theorem insert_slots_eq (hm₀ : BucketMapHashMap Int) (k₀ v₀ : Int) (new_slf₀ : BucketMapHashMap Int)
  (hslotseq : new_slf₀.slots =
    have a'₄ :=
      have a'₁ := k₀ % svec_len hm₀.slots
      have a'₂ := svec_get hm₀.slots a'₁
      have a'₃ := alist_aseq_contains_key a'₂ k₀
      svec_set hm₀.slots a'₁ (if a'₃ then alist_aseq_set a'₂ k₀ v₀ else alist_aseq_cons k₀ v₀ a'₂)
    if (bucket_map_total_len a'₄ > hm₀.max_load ∧ ¬hm₀.saturated) ∧
        svec_len a'₄ ≤ num_impl_11_MAX / 2 / hm₀.max_load_factor.dividend then
      bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len a'₄)) a'₄
    else a'₄)
  : new_slf₀.slots =
      if (bucket_map_total_len (insert hm₀.slots k₀ v₀) > hm₀.max_load ∧ ¬hm₀.saturated) ∧
          svec_len (insert hm₀.slots k₀ v₀) ≤ num_impl_11_MAX / 2 / hm₀.max_load_factor.dividend then
        bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len (insert hm₀.slots k₀ v₀)) : OVec (ASeq Int Int)) (insert hm₀.slots k₀ v₀)
      else insert hm₀.slots k₀ v₀ :=
  hslotseq

def BucketMapThmInsert_proof : BucketMapThmInsert := by
  unfold BucketMapThmInsert
  zap
  · rename_i hm₀ k₀ v₀ k2₀ v2₀
      hne hmaxload hge hlt hnumhm hdisthm huniqhm hposhm hk0ge0 hk20ge0
      new_slf₀ hmaxload' hge' hlt' hnumnew hdistnew huniqnew hposnew hfacteq hslotseq
    have hu : bucket_map_unique_keys (insert hm₀.slots k₀ v₀) := insert_preserves_unique hm₀.slots k₀ v₀ hposhm huniqhm
    have hd : bucket_map_keys_distributed_by_hash (insert hm₀.slots k₀ v₀) := insert_preserves_distributed hm₀.slots k₀ v₀ hposhm hdisthm
    have hposa4 : svec_len (insert hm₀.slots k₀ v₀) > 0 := by rw [insert_len_eq]; exact hposhm
    have hmatch_a4 : alist_aseq_key_matches (svec_get (insert hm₀.slots k₀ v₀) (k₀ % svec_len (insert hm₀.slots k₀ v₀))) k₀ v₀ := by
      rw [insert_len_eq]; exact insert_produces_key_matches hm₀.slots k₀ v₀ hposhm
    rw [insert_slots_eq hm₀ k₀ v₀ new_slf₀ hslotseq]
    exact resize_preserves_key_matches (insert hm₀.slots k₀ v₀) k₀ v₀ hu hd hposa4 _ hmatch_a4
  · rename_i hm₀ k₀ v₀ k2₀ v2₀
      hne hmaxload hge hlt hnumhm hdisthm huniqhm hposhm hk0ge0 hk20ge0
      new_slf₀ hmaxload' hge' hlt' hnumnew hdistnew huniqnew hposnew hfacteq hslotseq
    have hu : bucket_map_unique_keys (insert hm₀.slots k₀ v₀) := insert_preserves_unique hm₀.slots k₀ v₀ hposhm huniqhm
    have hd : bucket_map_keys_distributed_by_hash (insert hm₀.slots k₀ v₀) := insert_preserves_distributed hm₀.slots k₀ v₀ hposhm hdisthm
    have hposa4 : svec_len (insert hm₀.slots k₀ v₀) > 0 := by rw [insert_len_eq]; exact hposhm
    have hiff_a4 := insert_key_matches_iff hm₀.slots k2₀ v2₀ k₀ v₀ hposhm hne.symm
    rw [insert_slots_eq hm₀ k₀ v₀ new_slf₀ hslotseq]
    exact hiff_a4.trans (resize_key_matches_iff (insert hm₀.slots k₀ v₀) k2₀ v2₀ hu hd hposa4 _)
  · rename_i hm₀ k₀ v₀ k2₀ v2₀
      hne hmaxload hge hlt hnumhm hdisthm huniqhm hposhm hk0ge0 hk20ge0
      new_slf₀ hmaxload' hge' hlt' hnumnew hdistnew huniqnew hposnew hfacteq hslotseq
    have hu : bucket_map_unique_keys (insert hm₀.slots k₀ v₀) := insert_preserves_unique hm₀.slots k₀ v₀ hposhm huniqhm
    have hd : bucket_map_keys_distributed_by_hash (insert hm₀.slots k₀ v₀) := insert_preserves_distributed hm₀.slots k₀ v₀ hposhm hdisthm
    have hposa4 : svec_len (insert hm₀.slots k₀ v₀) > 0 := by rw [insert_len_eq]; exact hposhm
    have ha4len : bucket_map_total_len (insert hm₀.slots k₀ v₀) =
        bucket_map_total_len hm₀.slots + (if alist_aseq_contains_key (svec_get hm₀.slots (k₀ % svec_len hm₀.slots)) k₀ then 0 else 1) := by
      unfold insert
      rw [total_length_set hm₀.slots ⟨Int.emod_nonneg k₀ (by omega), Int.emod_lt_of_pos k₀ hposhm⟩]
      split <;> grind [svec_len_set1]
    rw [insert_slots_eq hm₀ k₀ v₀ new_slf₀ hslotseq] at hnumnew
    rw [resize_total_len (insert hm₀.slots k₀ v₀) hu hd hposa4] at hnumnew
    omega

end F
