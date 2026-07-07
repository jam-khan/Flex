import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure RangeUsizeRange  where
  mkRangeUsizeRange₀ ::
    start : Int 
    end_ : Int 
  deriving Inhabited
attribute [grind .] RangeUsizeRange.ext


end F
