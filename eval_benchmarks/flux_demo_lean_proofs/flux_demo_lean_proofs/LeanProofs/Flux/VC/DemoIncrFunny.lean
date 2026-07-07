import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoIncrFunny := 
 ∀ (n₀ : Int),
  ∀ (b₀ : Prop),
   (¬b₀) ->
    ((n₀ - 1) = (if b₀ then (n₀ + 1) else (n₀ - 1)))
end F
