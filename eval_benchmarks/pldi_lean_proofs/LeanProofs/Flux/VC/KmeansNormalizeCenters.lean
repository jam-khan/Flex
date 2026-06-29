import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmeansNormalizeCenters := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   (n₀ ≥ 0) ->
    (k₀ ≥ 0) ->
     (((k0 0 n₀ k₀))) ∧
     (∀ (i₀ : Int),
      ((k0 i₀ n₀ k₀)) ->
       (i₀ < k₀) ->
        (∀ (a'₁ : Int),
         (a'₁ = n₀) ->
          ((k1 a'₁ n₀ k₀ i₀))) ∧
        (∀ (a'₂ : Int),
         ((k1 a'₂ n₀ k₀ i₀)) ->
          (a'₂ = n₀)) ∧
        (∀ (a'₃ : Int),
         (a'₃ ≥ 0) ->
          ∀ (a'₄ : Int),
           ((k1 a'₄ n₀ k₀ i₀)) ->
            ((k0 (i₀ + 1) n₀ k₀)))
        )
     
end F
