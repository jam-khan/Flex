import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralInit0 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (n₀ ≥ 0) ->
     (((k0 f₀ 0 0 n₀ f₀))) ∧
     (∀ (f₁ : Int),
      ∀ (i₀ : Int),
       ∀ (res₀ : Int),
        ((k0 f₁ i₀ res₀ n₀ f₀)) ->
         ((¬(i₀ < n₀)) ->
          (res₀ = n₀)) ∧
         ((i₀ < n₀) ->
          (∀ (a'₄ : Int),
           ((k1 a'₄ n₀ f₀ f₁ i₀ res₀)) ->
            ∀ (a'₅ : Int),
             ((k2 a'₅ n₀ f₀ f₁ i₀ res₀)) ->
              (((0 ≤ a'₅)) ∧
              ((a'₅ < n₀))
              ) ∧
              (∀ (a'₆ : Int),
               ((k1 a'₆ n₀ f₀ f₁ i₀ res₀)) ->
                ∀ (a'₇ : Int),
                 ((k2 a'₇ n₀ f₀ f₁ i₀ res₀)) ->
                  (((0 ≤ a'₇)) ∧
                  ((a'₇ < n₀))
                  ) ∧
                  (∀ (a'₈ : Int),
                   ((k3 a'₈ n₀ f₀ f₁ i₀ res₀)))
                  )
              ) ∧
          (False ->
           ((c0) ∨ False)) ∧
          (((k1 f₁ n₀ f₀ f₁ i₀ res₀))) ∧
          (((k2 i₀ n₀ f₀ f₁ i₀ res₀))) ∧
          (∀ (a'₉ : Int),
           ((k3 a'₉ n₀ f₀ f₁ i₀ res₀)) ->
            ∀ (a'₁₀ : Int),
             ((k1 a'₁₀ n₀ f₀ f₁ i₀ res₀)) ->
              (0 ≤ (res₀ + 1)) ->
               ((k0 a'₁₀ (i₀ + 1) (res₀ + 1) n₀ f₀)))
          )
         )
     
end F
