import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmRemove
import Flex
import LeanProofs.User.Proof.Theorems
import LeanProofs.Tactics.KeyBounded
open Classical

namespace F

def BucketMapThmRemove_proof : BucketMapThmRemove := by
  unfold BucketMapThmRemove
  elim_leaves
  rename_i sleq
  split at sleq
  case isTrue =>
    rw [sleq, svec_get_set_eq]
    · apply unique_remove_nc
      grind
    · rw [svec_len_set2]
    · key_bounded
  case isFalse =>
    grind
end F
