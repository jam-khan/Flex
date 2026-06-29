import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmeansCentroid := 
 ∀ (n₀ : Int),
  ∀ (this₀ : Int),
   ∀ (this₁ : Int),
    (this₀ > 0) ->
     (this₁ > 0) ->
      (0 ≤ n₀) ->
       (this₀ ≥ 0) ->
        (this₁ ≥ 0) ->
         ((this₀ + this₁) > 0)
end F
