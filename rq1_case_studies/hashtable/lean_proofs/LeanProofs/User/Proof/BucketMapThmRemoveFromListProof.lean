import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmRemoveFromList
import LeanProofs.User.Proof.Theorems
import Flex
open Classical
set_option linter.unusedVariables false

namespace F

theorem remove_unchanged_ne (l : ASeq Int Int) : F.alist_aseq_keys_unchanged_except_k l (alist_aseq_remove_key l k) k := by
  fun_induction alist_aseq_remove_key
    <;> simp_all
    <;> grind

def BucketMapThmRemoveFromList_proof : BucketMapThmRemoveFromList := by
  unfold BucketMapThmRemoveFromList
  elim_leaves
  · grind [unique_remove_nc]
  · grind [remove_unchanged_ne]
  · grind [contains_remove_len, aseq_len_svec_len]

end F
