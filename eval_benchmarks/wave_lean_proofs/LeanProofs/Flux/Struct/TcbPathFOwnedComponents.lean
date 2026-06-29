import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure TcbPathFOwnedComponents  where
  mkTcbPathFOwnedComponents₀ ::
    size : Int 
    ns_prefix : Int 
    depth : Int 
    is_relative : Prop 
  deriving Inhabited
attribute [grind .] TcbPathFOwnedComponents.ext


end F
