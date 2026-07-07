import Surface.Real02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def AddMultTest := 
 ∀ (xx₀ : Real),
  ((xx₀ + xx₀) = (2.0 * xx₀))
end F
