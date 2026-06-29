import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def alist_aseq_key_matches : {t0 : Type} -> [Inhabited t0] -> {t1 : Type} -> [Inhabited t1] -> (ASeq t0 t1) -> t0 -> t1 -> Prop := sorry


end F
