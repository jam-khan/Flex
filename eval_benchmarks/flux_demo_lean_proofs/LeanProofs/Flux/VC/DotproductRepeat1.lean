import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DotproductRepeat1 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (n₀ ≥ 0) ->
     (((k0 f₀ 0 n₀ f₀))) ∧
     (∀ (f₁ : Int),
      ∀ (i₀ : Int),
       ((k0 f₁ i₀ n₀ f₀)) ->
        (i₀ < n₀) ->
         (∀ (a'₃ : Int),
          ((k1 a'₃ n₀ f₀ f₁ i₀)) ->
           ∀ (a'₄ : Int),
            ((k2 a'₄ n₀ f₀ f₁ i₀)) ->
             (((0 ≤ a'₄)) ∧
             ((a'₄ < n₀))
             ) ∧
             (∀ (a'₅ : Int),
              ((k1 a'₅ n₀ f₀ f₁ i₀)) ->
               ∀ (a'₆ : Int),
                ((k2 a'₆ n₀ f₀ f₁ i₀)) ->
                 (((0 ≤ a'₆)) ∧
                 ((a'₆ < n₀))
                 ) ∧
                 (((k3 n₀ f₀ f₁ i₀)))
                 )
             ) ∧
         (False ->
          ((c0) ∨ False)) ∧
         (((k1 f₁ n₀ f₀ f₁ i₀))) ∧
         (((k2 i₀ n₀ f₀ f₁ i₀))) ∧
         (((k3 n₀ f₀ f₁ i₀)) ->
          ∀ (a'₇ : Int),
           ((k1 a'₇ n₀ f₀ f₁ i₀)) ->
            ((k0 a'₇ (i₀ + 1) n₀ f₀)))
         )
     
end F
