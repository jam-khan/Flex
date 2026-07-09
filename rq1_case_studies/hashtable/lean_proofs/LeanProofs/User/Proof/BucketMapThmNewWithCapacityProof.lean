import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmNewWithCapacity
import Flex
open Classical
set_option linter.unusedVariables false


namespace F

def BucketMapThmNewWithCapacity_proof : BucketMapThmNewWithCapacity := by
  unfold BucketMapThmNewWithCapacity
  elim_leaves

end F
