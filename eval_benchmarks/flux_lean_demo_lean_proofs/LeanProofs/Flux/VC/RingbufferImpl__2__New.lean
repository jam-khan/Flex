import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RingbufferImpl__2__New := 
 ∀ (len₀ : Int),
  ∀ (f₀ : (SmtMap Int Prop)),
   (0 < len₀) ->
    ∀ (a'₀ : Int),
     ((0 ≤ a'₀) ∧ (a'₀ < 0)) ->
      (SmtMap_select (t0 := _) (t1 := _) f₀ a'₀)
end F
