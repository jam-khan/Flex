import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.AlistImpl__0__ReplaceIfPresent
import Flex
open Classical

namespace F

def AlistImpl__0__ReplaceIfPresent_proof : AlistImpl__0__ReplaceIfPresent := by
  unfold AlistImpl__0__ReplaceIfPresent
  fusion ; elim_leaves

end F
