import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__InsertInList
import Flex
open Classical

namespace F

def BucketMapImpl__0__InsertInList_proof : BucketMapImpl__0__InsertInList := by
  unfold BucketMapImpl__0__InsertInList
  fusion ; elim_leaves

end F
