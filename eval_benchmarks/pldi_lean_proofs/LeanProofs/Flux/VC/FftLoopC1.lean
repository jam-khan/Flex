import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FftLoopC1 := 
 ∀ (j₀ : Int),
  ∀ (k₀ : Int),
   (0 ≤ j₀) ->
    (0 ≤ k₀) ->
     (j₀ ≥ 0) ->
      (k₀ ≥ 0) ->
       ((¬(j₀ ≤ k₀)) ->
        (((j₀ - k₀) ≥ 0)) ∧
        (((0 ≤ (j₀ - k₀))) ∧
        ((0 ≤ (k₀ / 2))) ∧
        (∀ (v₀ : Int),
         (v₀ ≤ ((k₀ / 2) + (k₀ / 2))) ->
          (v₀ ≥ 0) ->
           (v₀ ≤ (k₀ + k₀)))
        )
        ) ∧
       ((j₀ ≤ k₀) ->
        ((j₀ + k₀) ≤ (k₀ + k₀)))
       
end F
