import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure NeuralLayer  where
  mkNeuralLayer₀ ::
    i : Int 
    o : Int 
  deriving Inhabited
attribute [grind .] NeuralLayer.ext


end F
