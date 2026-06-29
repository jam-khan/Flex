import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.ASeq
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def bucket_map_disjoint_with_list : {t0 : Type} -> [Inhabited t0] -> (OVec (ASeq Int t0)) -> (ASeq Int t0) -> Prop := sorry


end F
