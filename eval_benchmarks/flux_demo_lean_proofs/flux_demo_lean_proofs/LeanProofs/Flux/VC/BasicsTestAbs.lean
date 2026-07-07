import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BasicsTestAbs := ∃ k0 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ((0 ≤ y₀) ∧ (x₀ ≤ y₀)) ->
    ((¬(y₀ ≥ 0)) ->
     ((k0 False x₀ y₀))) ∧
    ((y₀ ≥ 0) ->
     ((k0 (y₀ ≥ x₀) x₀ y₀))) ∧
    (∀ (a'₂ : Prop),
     ((k0 a'₂ x₀ y₀)) ->
      (a'₂ = True))
    
end F
