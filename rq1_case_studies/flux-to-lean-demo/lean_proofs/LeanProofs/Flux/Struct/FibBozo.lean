import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure FibBozo  where
  mkFibBozo₀ ::
    x : Int 
    y : Prop 
  deriving Inhabited
attribute [grind .] FibBozo.ext


end F
