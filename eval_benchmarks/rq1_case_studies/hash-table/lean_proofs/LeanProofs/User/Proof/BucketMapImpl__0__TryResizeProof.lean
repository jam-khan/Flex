import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__TryResize
import LeanProofs.User.Proof.Theorems
import LeanFixpoint
open Classical

namespace F

theorem num_entries_preserved (v : OVec (ASeq Int Int))
  (h0 : n > 0)
  (h1 : bucket_map_keys_distributed_by_hash v)
  (h2 : bucket_map_unique_keys v)
  : bucket_map_total_len (bucket_map_absorb_buckets (bucket_map_empties n) v) = bucket_map_total_len v := by
    rw [no_overlap_num_entries_preserved]
    rw [total_len_empties] ; omega
    all_goals grind

attribute [grind .] num_entries_preserved

theorem resize_total_len (a4 : OVec (ASeq Int Int))
  (hu : bucket_map_unique_keys a4) (hd : bucket_map_keys_distributed_by_hash a4) (hpos : svec_len a4 > 0)
  (cond : Prop) [Decidable cond]
  : bucket_map_total_len (if cond then bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len a4)) a4 else a4)
      = bucket_map_total_len a4 := by
    split
    · exact num_entries_preserved a4 (by omega) hd hu
    · rfl

theorem resize_preserves_key_matches (a4 : OVec (ASeq Int Int)) (key val : Int)
  (hu : bucket_map_unique_keys a4) (hd : bucket_map_keys_distributed_by_hash a4) (hpos : svec_len a4 > 0)
  (cond : Prop) [Decidable cond]
  (h : alist_aseq_key_matches (svec_get a4 (key % svec_len a4)) key val)
  : alist_aseq_key_matches
      (svec_get (if cond then bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len a4)) a4 else a4)
        (key % svec_len (if cond then bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len a4)) a4 else a4)))
      key val := by
    split
    · exact mem_absorb_buckets_key_matches_preserved_from_bs (bucket_map_empties (2 * svec_len a4)) a4
        key val hu hd hpos (empties_pos _ (by omega)) h
    · exact h

theorem resize_key_matches_iff (a4 : OVec (ASeq Int Int)) (key val : Int)
  (hu : bucket_map_unique_keys a4) (hd : bucket_map_keys_distributed_by_hash a4) (hpos : svec_len a4 > 0)
  (cond : Prop) [Decidable cond]
  : alist_aseq_key_matches (svec_get a4 (key % svec_len a4)) key val ↔
    alist_aseq_key_matches
      (svec_get (if cond then bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len a4)) a4 else a4)
        (key % svec_len (if cond then bucket_map_absorb_buckets (bucket_map_empties (2 * svec_len a4)) a4 else a4)))
      key val := by
    constructor
    · exact resize_preserves_key_matches a4 key val hu hd hpos cond
    · intro h
      split at h
      · have hres := mem_absorb_buckets_key_matches (bucket_map_empties (2 * svec_len a4)) a4
          (empties_unique _) (empties_distributed _) (empties_pos _ (by omega)) hu hd h
        rcases hres with hl | hr
        · exact absurd hl (no_match_in_empties _ _ key val)
        · exact hr
      · exact h

def BucketMapImpl__0__TryResize_proof : BucketMapImpl__0__TryResize := by
  unfold BucketMapImpl__0__TryResize
  zap

end F
