import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__Insert
import Flex
open Classical

namespace F

attribute [grind .] BucketMapFraction.ext
def BucketMapImpl__0__Insert_proof : BucketMapImpl__0__Insert := by
  unfold BucketMapImpl__0__Insert
  fusion ; elim_leaves

end F
