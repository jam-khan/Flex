import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.SvecLen
open Classical
set_option linter.unusedVariables false


namespace F

@[simp, grind]
noncomputable def bucket_map_disjoint_with_list : {t0 : Type} -> [Inhabited t0] -> (OVec (ASeq Int t0)) -> (ASeq Int t0) -> Prop :=
  fun s l =>
    ∀ b1 e1 e2, b1 ∈ s → e1 ∈ b1 → e2 ∈ l → e1.fst ≠ e2.fst


end F
