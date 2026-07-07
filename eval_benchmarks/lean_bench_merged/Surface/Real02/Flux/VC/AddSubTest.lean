import Surface.Real02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def AddSubTest := 
 ∀ (xx₀ : Real),
  ∀ (yy₀ : Real),
   (((xx₀ + yy₀) - yy₀) = xx₀)
end F
