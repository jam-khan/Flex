import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure TypesNativeIoVec  where
  mkTypesNativeIoVec₀ ::
    iov_base : Int 
    iov_len : Int 
  deriving Inhabited
attribute [grind .] TypesNativeIoVec.ext


end F
