import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BorrowsDecr := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (v₀ > 0) ->
    (0 ≤ (v₀ - 1))
end F
