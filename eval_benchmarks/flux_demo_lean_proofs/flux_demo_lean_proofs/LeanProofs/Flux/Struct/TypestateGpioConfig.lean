import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure TypestateGpioConfig  where
  mkTypestateGpioConfig₀ ::
    enabled : Prop 
    direction : Prop 
    mode : Int 
  deriving Inhabited
attribute [grind .] TypestateGpioConfig.ext


end F
