import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__Remove
import LeanProofs.Tactics.KeyBounded
import Flex
import LeanProofs.User.Proof.Theorems
open Classical

namespace F

set_option maxHeartbeats 500000

def BucketMapImpl__0__Remove_proof : BucketMapImpl__0__Remove := by
  unfold BucketMapImpl__0__Remove
  fusion
  intros slf key
  elim_leaves
  · apply Int.emod_lt_of_pos
    omega
  · simp at * ; apply Int.emod_lt_of_pos
    omega
  · rename_i n1 n2 n3 issome hissomedef hsomeimp hnsomeimp histrue n9 n10
    have hcontains : alist_aseq_contains_key (svec_get slf.slots (key % svec_len slf.slots)) key := by
      rw [← hissomedef, histrue]
      trivial
    have hne : svec_get slf.slots (key % svec_len slf.slots) ≠ alist_aseq_nil := by
      intro h
      rw [h] at hcontains
      simp [alist_aseq_contains_key, alist_aseq_nil] at hcontains
    have hlen : 1 ≤ (svec_get slf.slots (key % svec_len slf.slots)).length := by
      rcases hcase : svec_get slf.slots (key % svec_len slf.slots) with _ | ⟨hd, tl⟩
      · exact absurd hcase hne
      · simp
    have hmem : svec_get slf.slots (key % svec_len slf.slots) ∈ slf.slots := by
      have hlt : key % svec_len slf.slots < svec_len slf.slots := by apply Int.emod_lt_of_pos; omega
      have hge : 0 ≤ key % svec_len slf.slots := by apply Int.emod_nonneg; omega
      unfold svec_get svec_len at *
      grind
    have hsum : (svec_get slf.slots (key % svec_len slf.slots)).length ≤ (List.map List.length slf.slots).sum :=
      elem_le_sum _ (List.mem_map_of_mem hmem)
    unfold bucket_map_total_len at *
    omega
  · rw [svec_set_set, total_length_set]
    rename_i lsres issome hissomedef hsomeimp hnsomeimp aux1 aux2
    grind [contains_remove_len]
    key_bounded
  · unfold bucket_map_keys_distributed_by_hash
    rw [svec_len_set2, svec_len_set2, svec_set_set]
    rename_i lsres issome hissomedef hsomeimp hnsomeimp aux1 aux2 aux3
    intro i k ⟨ilb, iub⟩ hcontains
    by_cases ieq : i = key % svec_len slf.slots
    · subst ieq
      rw [svec_get_set_eq slf.slots rfl ⟨by apply Int.emod_nonneg; omega, by apply Int.emod_lt_of_pos; omega⟩] at hcontains
      by_cases hs : issome
      · rw [hsomeimp hs] at hcontains
        simp only [alist_aseq_contains_key, List.mem_map] at hcontains
        rcases hcontains with ⟨⟨k', x⟩, hx, hkx⟩
        simp only at hkx
        rw [hkx] at hx
        have := alist_remove_contains_contains _ hx
        exact (by assumption : bucket_map_keys_distributed_by_hash slf.slots) _ k ⟨ilb, iub⟩ this
      · rw [hnsomeimp hs] at hcontains
        exact (by assumption : bucket_map_keys_distributed_by_hash slf.slots) _ k ⟨ilb, iub⟩ hcontains
    · rw [svec_get_set_ne slf.slots (Ne.symm ieq) (by apply Int.emod_nonneg; omega) (by omega)] at hcontains
      exact (by assumption : bucket_map_keys_distributed_by_hash slf.slots) i k ⟨ilb, iub⟩ hcontains
  · unfold bucket_map_unique_keys
    rw [svec_set_set]
    rename_i lsres issome hissomedef hsomeimp hnsomeimp aux1 aux2 aux3
    intro bucket hbucketmem
    have hbase : alist_aseq_unique_keys (svec_get slf.slots (key % svec_len slf.slots)) := by
      have hlt : key % svec_len slf.slots < svec_len slf.slots := by apply Int.emod_lt_of_pos; omega
      have hge : 0 ≤ key % svec_len slf.slots := by apply Int.emod_nonneg; omega
      have hmem : svec_get slf.slots (key % svec_len slf.slots) ∈ slf.slots := by
        unfold svec_get svec_len at *
        grind
      exact (by assumption : bucket_map_unique_keys slf.slots) _ hmem
    have hres : alist_aseq_unique_keys lsres := by
      by_cases hs : issome
      · rw [hsomeimp hs]
        exact unique_remove_unique _ hbase
      · rw [hnsomeimp hs]
        exact hbase
    rw [List.mem_iff_getElem] at hbucketmem
    obtain ⟨i, hi, hbucket⟩ := hbucketmem
    by_cases ieq2 : i = (key % svec_len slf.slots).toNat
    · subst ieq2
      rw [← hbucket]
      simp only [svec_set]
      rw [List.getElem_set_self]
      exact hres
    · rw [← hbucket]
      simp only [svec_set]
      rw [List.getElem_set_ne (Ne.symm ieq2)]
      apply (by assumption : bucket_map_unique_keys slf.slots)
      unfold svec_get svec_len at *
      grind
  · rw [svec_set_set]
    rename_i lsres issome hissomedef hsomeimp hnsomeimp aux1 aux2 aux3
    by_cases hs : issome
    · rw [hsomeimp hs]
      have haux : aux1 = True := by grind
      rw [haux, if_pos trivial]
    · rw [hnsomeimp hs]
      have haux : aux1 = False := by grind
      rw [haux, if_neg (by simp)]
      apply set_get_eq
      exact ⟨by apply Int.emod_nonneg; omega, by apply Int.emod_lt_of_pos; omega⟩
end F
