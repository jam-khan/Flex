import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoTest := 
 ∀ (v₀ : Int),
  ((0 ≤ v₀) ∧ ((-5) ≤ v₀)) ->
   (((v₀ ≥ 0) = True)) ∧
   (∀ (v₁ : Int),
    ((0 ≤ v₁) ∧ (5 ≤ v₁)) ->
     (((v₁ ≥ 5) = True)) ∧
     ((((4 + 1) = 5) = True))
     )
   
end F
