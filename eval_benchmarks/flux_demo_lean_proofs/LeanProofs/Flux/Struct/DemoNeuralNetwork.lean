import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure DemoNeuralNetwork  where
  mkDemoNeuralNetwork₀ ::
    i : Int 
    o : Int 
  deriving Inhabited
attribute [grind .] DemoNeuralNetwork.ext


end F
