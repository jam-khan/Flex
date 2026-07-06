import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def bucket_map_disjoint : {t0 : Type} -> [Inhabited t0] -> (OVec (ASeq Int t0)) -> (OVec (ASeq Int t0)) -> Prop :=
  fun v1 v2 =>
    ∀ b1 b2 e1 e2, b1 ∈ v1 → b2 ∈ v2 → e1 ∈ b1 → e2 ∈ b2 → e1.fst ≠ e2.fst


end F
