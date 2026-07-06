import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__InsertNoResize
import LeanProofs.Tactics.KeyBounded
import LeanFixpoint
import LeanProofs.User.Proof.Theorems
open Classical

namespace F

def BucketMapImpl__0__InsertNoResize_proof : BucketMapImpl__0__InsertNoResize := by
  unfold BucketMapImpl__0__InsertNoResize
  fusion
  intros slf key val
  zap
  · apply Int.emod_lt_of_pos ; omega
  · rw [svec_len_set2]
    apply Int.emod_lt_of_pos ; omega
  · split_hyps
    all_goals (
      rw [
        svec_set_set,
        total_length_set
      ]
      grind [svec_len_set1]
      key_bounded
    )
  · unfold bucket_map_keys_distributed_by_hash
    rw [svec_len_set2, svec_len_set2, svec_set_set]
    rename_i lsres inserted hinsdef hconsimp hsetimp aux1 aux2
    intro i k ⟨ilb, iub⟩ hcontains
    by_cases ieq : i = key % svec_len slf.slots
    · subst ieq
      rw [svec_get_set_eq slf.slots rfl ⟨by apply Int.emod_nonneg; omega, by apply Int.emod_lt_of_pos; omega⟩] at hcontains
      by_cases hins : inserted
      · rw [hconsimp hins] at hcontains
        simp only [alist_aseq_contains_key, alist_aseq_cons, List.map_cons, List.mem_cons] at hcontains
        rcases hcontains with hk | hk
        · rw [hk]
        · exact (by assumption : bucket_map_keys_distributed_by_hash slf.slots) _ k ⟨ilb, iub⟩ hk
      · rw [hsetimp hins] at hcontains
        by_cases keq : k = key
        · rw [keq]
        · simp only [alist_aseq_contains_key, List.mem_map] at hcontains
          rcases hcontains with ⟨⟨k', x⟩, hx, hkx⟩
          simp only at hkx
          rw [hkx] at hx
          have := alist_set_contains_contains _ hx
          exact (by assumption : bucket_map_keys_distributed_by_hash slf.slots) _ k ⟨ilb, iub⟩ this
    · rw [svec_get_set_ne slf.slots (Ne.symm ieq) (by apply Int.emod_nonneg; omega) (by omega)] at hcontains
      exact (by assumption : bucket_map_keys_distributed_by_hash slf.slots) i k ⟨ilb, iub⟩ hcontains
  · unfold bucket_map_unique_keys
    rw [svec_set_set]
    rename_i lsres inserted hinsdef hconsimp hsetimp aux1 aux2
    intro bucket hbucketmem
    have hbase : alist_aseq_unique_keys (svec_get slf.slots (key % svec_len slf.slots)) := by
      have hlt : key % svec_len slf.slots < svec_len slf.slots := by apply Int.emod_lt_of_pos; omega
      have hge : 0 ≤ key % svec_len slf.slots := by apply Int.emod_nonneg; omega
      have hmem : svec_get slf.slots (key % svec_len slf.slots) ∈ slf.slots := by
        unfold svec_get svec_len at *
        grind
      exact (by assumption : bucket_map_unique_keys slf.slots) _ hmem
    have hres : alist_aseq_unique_keys lsres := by
      by_cases hins : inserted
      · have hnc : ¬alist_aseq_contains_key (svec_get slf.slots (key % svec_len slf.slots)) key := by
          rw [hinsdef] at hins
          exact hins
        rw [hconsimp hins]
        exact unique_nc_cons_nc _ hbase hnc
      · rw [hsetimp hins]
        exact unique_set_uniqe _ hbase
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
    rename_i lsres inserted hinsdef hconsimp hsetimp aux1 aux2
    by_cases hins : inserted
    · rw [hconsimp hins]
      have hnc : ¬alist_aseq_contains_key (svec_get slf.slots (key % svec_len slf.slots)) key := by
        rw [hinsdef] at hins; exact hins
      simp only [alist_aseq_contains_key, List.mem_map] at hnc
      unfold svec_get svec_len alist_aseq_cons at *
      grind
    · rw [hsetimp hins]
      have hc : alist_aseq_contains_key (svec_get slf.slots (key % svec_len slf.slots)) key := by
        rw [hinsdef] at hins; exact not_not.mp hins
      simp only [alist_aseq_contains_key, List.mem_map] at hc
      unfold svec_get svec_len alist_aseq_set at *
      grind
end F
