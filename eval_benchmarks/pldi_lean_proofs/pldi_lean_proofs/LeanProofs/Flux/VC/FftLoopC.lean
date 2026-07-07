import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FftLoopC := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (2 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (((n₀ - 1) ≥ 0)) ∧
    (((k0 1 1 n₀))) ∧
    (∀ (i₀ : Int),
     ∀ (j₀ : Int),
      ((k0 i₀ j₀ n₀)) ->
       (i₀ < (n₀ - 1)) ->
        ((¬(i₀ < j₀)) ->
         ((k1 n₀ i₀ j₀))) ∧
        ((i₀ < j₀) ->
         ((j₀ < n₀)) ∧
         ((i₀ < n₀)) ∧
         ((j₀ < n₀)) ∧
         ((i₀ < n₀)) ∧
         ((j₀ < n₀)) ∧
         ((i₀ < n₀)) ∧
         ((j₀ < n₀)) ∧
         ((i₀ < n₀)) ∧
         (((k1 n₀ i₀ j₀)))
         ) ∧
        (((k1 n₀ i₀ j₀)) ->
         ((0 ≤ j₀)) ∧
         ((0 ≤ ((n₀ - 1) / 2))) ∧
         (∀ (v₀ : Int),
          (v₀ ≤ (((n₀ - 1) / 2) + ((n₀ - 1) / 2))) ->
           (v₀ ≥ 0) ->
            ((k0 (i₀ + 1) v₀ n₀)))
         )
        )
    
end F
