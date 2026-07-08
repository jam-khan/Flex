import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmMoveElements
import LeanProofs.User.Proof.Theorems
import Flex
open Classical
set_option linter.unusedVariables false


namespace F

def BucketMapThmMoveElements_proof : BucketMapThmMoveElements := by
  unfold BucketMapThmMoveElements
  elim_leaves
  · grind [mem_absorb_buckets_key_matches]
  · grind [mem_absorb_buckets_key_matches_preserved]
  · grind [absorb_buckets_key_matches_of_mem, key_matches_mem, bucket_mem_of_pos, List.mem_flatten]
  · rename_i hm₀ s₀ _k₀ _v₀
      hdisj hunique hdist _ _ _ h_num_entries _ _ h_pos _
      new_t₀ _ _ _ h_num_entries' _ _ _ _ _ _ h_slots_eq
    rw [h_slots_eq, no_overlap_num_entries_preserved hm₀.slots s₀ hdisj h_pos hdist hunique] at h_num_entries'
    omega

end F
