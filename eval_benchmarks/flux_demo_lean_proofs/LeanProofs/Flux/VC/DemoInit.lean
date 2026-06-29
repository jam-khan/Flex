import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoInit := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (n₀ ≥ 0) ->
     (((k0 f₀ 0 0 n₀ f₀))) ∧
     (∀ (f₁ : Int),
      ∀ (res₀ : Int),
       ∀ (i₀ : Int),
        ((k0 f₁ res₀ i₀ n₀ f₀)) ->
         ((¬(i₀ < n₀)) ->
          (res₀ = n₀)) ∧
         ((i₀ < n₀) ->
          (∀ (a'₄ : Int),
           ((k1 a'₄ n₀ f₀ f₁ res₀ i₀)) ->
            ∀ (a'₅ : Int),
             ((k2 a'₅ n₀ f₀ f₁ res₀ i₀)) ->
              ∀ (a'₆ : Int),
               ((k1 a'₆ n₀ f₀ f₁ res₀ i₀)) ->
                ∀ (a'₇ : Int),
                 ((k2 a'₇ n₀ f₀ f₁ res₀ i₀)) ->
                  ∀ (a'₈ : Int),
                   ((k3 a'₈ n₀ f₀ f₁ res₀ i₀))) ∧
          (False ->
           ((c0) ∨ False)) ∧
          (((k1 f₁ n₀ f₀ f₁ res₀ i₀))) ∧
          (((k2 i₀ n₀ f₀ f₁ res₀ i₀))) ∧
          (∀ (a'₉ : Int),
           ((k3 a'₉ n₀ f₀ f₁ res₀ i₀)) ->
            ∀ (a'₁₀ : Int),
             ((k1 a'₁₀ n₀ f₀ f₁ res₀ i₀)) ->
              (0 ≤ (res₀ + 1)) ->
               ((k0 a'₁₀ (res₀ + 1) (i₀ + 1) n₀ f₀)))
          )
         )
     
end F
