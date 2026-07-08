import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__RemoveFromList
import Flex
open Classical

namespace F

def BucketMapImpl__0__RemoveFromList_proof : BucketMapImpl__0__RemoveFromList := by
  unfold BucketMapImpl__0__RemoveFromList
  fusion ; elim_leaves
end F
