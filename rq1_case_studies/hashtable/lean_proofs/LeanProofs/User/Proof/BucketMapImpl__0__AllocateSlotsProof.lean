import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__AllocateSlots
import LeanProofs.User.Proof.Qualifs
import Flex
open Classical

namespace F

attribute [grind .] List.eq_replicate_iff

def BucketMapImpl__0__AllocateSlots_proof : BucketMapImpl__0__AllocateSlots := by
  solve_fixpoint
end F
