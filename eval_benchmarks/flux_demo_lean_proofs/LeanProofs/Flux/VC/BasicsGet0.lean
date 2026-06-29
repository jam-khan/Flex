import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BasicsGet0 := 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (n₀ ≥ 0) ->
    (0 < n₀)
end F
