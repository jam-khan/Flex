import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__NewWithCapacity
import LeanProofs.User.Proof.Theorems
import LeanFixpoint
open Classical

namespace F

attribute [grind .] total_len_empties
def BucketMapImpl__0__NewWithCapacity_proof : BucketMapImpl__0__NewWithCapacity := by
  unfold BucketMapImpl__0__NewWithCapacity
  zap ; simp_all

end F
