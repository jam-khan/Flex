import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

def Arr (t0 : Type) [Inhabited t0] : Type := Int → t0

instance [Inhabited t0] : Inhabited (Arr t0) where
  default := fun _ => default

end F
