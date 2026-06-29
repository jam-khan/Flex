import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure DemoLayer  where
  mkDemoLayer₀ ::
    i : Int 
    o : Int 
  deriving Inhabited
attribute [grind .] DemoLayer.ext


end F
