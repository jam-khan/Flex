import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.ASeq
open Classical

namespace F

@[simp, grind]
noncomputable def alist_aseq_remove_key : {t0 : Type} -> [Inhabited t0] -> {t1 : Type} -> [Inhabited t1] -> (ASeq t0 t1) -> t0 -> (ASeq t0 t1) :=
  fun l k => match l with
    | .nil => .nil
    | (k', v')::rest => if k == k' then rest else (k', v')::(alist_aseq_remove_key rest k)


end F
