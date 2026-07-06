import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmMoveElementsFromList
import LeanFixpoint
import LeanProofs.User.Proof.Theorems
open Classical
set_option linter.unusedVariables false


namespace F

def BucketMapThmMoveElementsFromList_proof : BucketMapThmMoveElementsFromList := by
  unfold BucketMapThmMoveElementsFromList
  zap
  · grind [mem_absorb_key_matches]
  · grind [mem_absorb_key_matches_preserved]
  · grind [absorb_key_matches_of_mem, key_matches_mem]
  · grind [no_overlap_num_entries_preserved1]

end F
