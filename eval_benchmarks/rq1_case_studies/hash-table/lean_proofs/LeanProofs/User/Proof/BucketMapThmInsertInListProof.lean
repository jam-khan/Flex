import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmInsertInList
import LeanFixpoint
import LeanProofs.User.Proof.Theorems
set_option linter.unusedVariables false

namespace F

attribute [grind .] alist_set_matches key_matches_set_ne unique_nc_cons_nc unique_set_uniqe

def BucketMapThmInsertInList_proof : BucketMapThmInsertInList := by
  unfold BucketMapThmInsertInList
  intro k v ls
  zap
  grind [svec_len_set1]

end F
