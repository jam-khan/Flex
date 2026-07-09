import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
open Classical

namespace F

@[simp, grind]
noncomputable def svec_empty : {t0 : Type} -> [Inhabited t0] -> (OVec t0) := []


end F
