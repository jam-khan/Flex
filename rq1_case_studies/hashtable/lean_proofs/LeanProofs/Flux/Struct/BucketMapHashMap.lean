import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure BucketMapHashMap (t0 : Type) [Inhabited t0] where
  mkBucketMapHashMap₀ ::
    num_entries : Int 
    max_load_factor : BucketMapFraction 
    max_load : Int 
    saturated : Prop 
    slots : (OVec (ASeq Int t0)) 
  deriving Inhabited
attribute [grind .] BucketMapHashMap.ext


end F
