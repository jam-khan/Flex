import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__New := 
 ∀ (len₀ : Int),
  (0 < len₀) ->
   ∀ (i₀ : Int),
    (False = ((0 ≤ i₀) ∧ (i₀ < 0)))
end F
