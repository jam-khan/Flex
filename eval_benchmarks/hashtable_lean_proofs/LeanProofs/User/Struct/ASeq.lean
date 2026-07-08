import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

def ASeq (t0 : Type) [Inhabited t0] (t1 : Type) [Inhabited t1] : Type := List (t0 × t1)

instance [Inhabited t0] [Inhabited t1] : Inhabited (ASeq t0 t1) where
  default := []

end F
