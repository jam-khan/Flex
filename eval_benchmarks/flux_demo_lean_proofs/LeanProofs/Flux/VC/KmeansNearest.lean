import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmeansNearest := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (k₀ : Int),
  ∀ (n₀ : Int),
   (k₀ > 0) ->
    (0 ≤ k₀) ->
     (0 ≤ n₀) ->
      (∀ (a'₀ : Int),
       ∀ (a'₁ : Int),
        ((k0 a'₀ a'₁ k₀ n₀)) ->
         (0 ≤ a'₀) ->
          (0 ≤ a'₁) ->
           (a'₁ = a'₀)) ∧
      (∀ (a'₂ : Int),
       ((k1 a'₂ k₀ n₀)) ->
        ∀ (a'₃ : Int),
         ((k2 a'₃ k₀ n₀)) ->
          ((k0 a'₂ a'₃ k₀ n₀))) ∧
      (∀ (a'₄ : Int),
       (a'₄ = n₀) ->
        ((k2 a'₄ k₀ n₀))) ∧
      (((k1 n₀ k₀ n₀))) ∧
      ((0 < k₀))
      
end F
