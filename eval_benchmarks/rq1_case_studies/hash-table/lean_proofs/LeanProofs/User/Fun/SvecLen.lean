import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
open Classical

namespace F

@[simp, grind]
noncomputable def svec_len : {t0 : Type} -> [Inhabited t0] -> (OVec t0) -> Int :=
  fun v => v.length


end F
