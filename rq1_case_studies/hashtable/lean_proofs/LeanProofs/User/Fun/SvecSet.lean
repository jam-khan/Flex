import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.OVec
open Classical

namespace F

@[simp, grind]
noncomputable def svec_set : {t0 : Type} -> [Inhabited t0] -> (OVec t0) -> Int -> t0 -> (OVec t0) :=
  fun v i e => v.set i.toNat e


end F
