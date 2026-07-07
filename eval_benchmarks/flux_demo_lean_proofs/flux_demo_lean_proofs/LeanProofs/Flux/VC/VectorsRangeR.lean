import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsRangeR := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ ≤ hi₀) ->
    (lo₀ ≥ 0) ->
     (hi₀ ≥ 0) ->
      ((¬(lo₀ ≥ hi₀)) ->
       (((lo₀ + 1) ≤ hi₀)) ∧
       ((0 ≤ (hi₀ - (lo₀ + 1))) ->
        (∀ (v₀ : Int),
         (((lo₀ + 1) ≤ v₀) ∧ (v₀ < hi₀)) ->
          ((k0 v₀ lo₀ hi₀))) ∧
        (((k0 lo₀ lo₀ hi₀))) ∧
        ((0 ≤ ((hi₀ - (lo₀ + 1)) + 1)) ->
         (∀ (a'₁ : Int),
          ((k0 a'₁ lo₀ hi₀)) ->
           ((lo₀ ≤ a'₁)) ∧
           ((a'₁ < hi₀))
           ) ∧
         ((((hi₀ - (lo₀ + 1)) + 1) = (hi₀ - lo₀)))
         )
        )
       ) ∧
      ((lo₀ ≥ hi₀) ->
       (0 = (hi₀ - lo₀)))
      
end F
