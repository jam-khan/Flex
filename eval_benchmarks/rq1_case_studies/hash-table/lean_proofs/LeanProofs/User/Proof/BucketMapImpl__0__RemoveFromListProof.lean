import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__RemoveFromList
import LeanFixpoint
open Classical

namespace F

def BucketMapImpl__0__RemoveFromList_proof : BucketMapImpl__0__RemoveFromList := by
  unfold BucketMapImpl__0__RemoveFromList
  fusion ; zap
end F
