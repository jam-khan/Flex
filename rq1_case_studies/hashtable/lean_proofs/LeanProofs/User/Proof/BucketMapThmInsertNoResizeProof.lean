import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmInsertNoResize
import LeanProofs.User.Proof.Theorems
import LeanProofs.Tactics.KeyBounded
import Flex
open Classical

namespace F

theorem cons_matches (l : ASeq Int Int)
  : alist_aseq_key_matches (alist_aseq_cons k v l) k v := by
    simp

def BucketMapThmInsertNoResize_proof : BucketMapThmInsertNoResize := by
  unfold BucketMapThmInsertNoResize
  intros hm k v
  elim_leaves
  rename_i sleq
  rw [sleq, svec_get_set_eq]
  split ; rename_i h
  · grind only [alist_set_matches]
  · grind only [!cons_matches]
  · rw [svec_len_set2]
  · key_bounded

end F
