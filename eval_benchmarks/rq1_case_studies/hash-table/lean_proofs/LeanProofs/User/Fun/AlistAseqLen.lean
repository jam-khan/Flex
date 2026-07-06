import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
open Classical

namespace F

@[simp, grind]
noncomputable def alist_aseq_len : {t0 : Type} -> [Inhabited t0] -> {t1 : Type} -> [Inhabited t1] -> (ASeq t0 t1) -> Int :=
  fun l => l.length


end F
