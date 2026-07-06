import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.BucketMapAbsorbBucket
open Classical

namespace F

@[simp, grind]
noncomputable def bucket_map_absorb_buckets : {t0 : Type} -> [Inhabited t0] -> (OVec (ASeq Int t0)) -> (OVec (ASeq Int t0)) -> (OVec (ASeq Int t0)) :=
  fun v bs => match bs with
    | .nil => v
    | b::bs => bucket_map_absorb_buckets (bucket_map_absorb_bucket v b) bs


end F
