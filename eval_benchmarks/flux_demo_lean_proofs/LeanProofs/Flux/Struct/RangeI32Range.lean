import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure RangeI32Range  where
  mkRangeI32Range₀ ::
    start : Int 
    end_ : Int 
  deriving Inhabited
attribute [grind .] RangeI32Range.ext


end F
