import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BasicsLet2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (a'₀ : Prop),
   (a'₀ = True) ->
    ∀ (a'₁ : Int),
     (n₀ < a'₁) ->
      ∀ (a'₂ : Prop),
       (a'₂ = True) ->
        ∀ (a'₃ : Int),
         (a'₁ < a'₃) ->
          (((k0 a'₃ n₀ a'₀ a'₁ a'₂ a'₃))) ∧
          (∀ (a'₄ : Int),
           ((k0 a'₄ n₀ a'₀ a'₁ a'₂ a'₃)) ->
            (n₀ < a'₄))
          
end F
