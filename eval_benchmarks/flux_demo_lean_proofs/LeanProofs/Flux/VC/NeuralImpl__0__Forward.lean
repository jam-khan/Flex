import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.NeuralLayer
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralImpl__0__Forward := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (l₀ : NeuralLayer),
  (0 ≤ (NeuralLayer.i l₀)) ->
   ((NeuralLayer.i l₀) ≥ 0) ->
    ((NeuralLayer.o l₀) ≥ 0) ->
     (0 ≤ (NeuralLayer.o l₀)) ->
      (∀ (a'₀ : Int),
       ((k0 a'₀ (NeuralLayer.i l₀) (NeuralLayer.o l₀))) ->
        (a'₀ ≥ 0) ->
         ((a'₀ < (NeuralLayer.o l₀))) ∧
         (∀ (a'₁ : Int),
          (a'₁ = (NeuralLayer.i l₀)) ->
           ((k1 a'₁ (NeuralLayer.i l₀) (NeuralLayer.o l₀) a'₀))) ∧
         (∀ (a'₂ : Int),
          ((k1 a'₂ (NeuralLayer.i l₀) (NeuralLayer.o l₀) a'₀)) ->
           (0 ≤ a'₂) ->
            (((NeuralLayer.i l₀) = a'₂)) ∧
            ((a'₀ < (NeuralLayer.o l₀))) ∧
            ((a'₀ < (NeuralLayer.o l₀)))
            )
         ) ∧
      (∀ (item₀ : Int),
       ((0 ≤ item₀) ∧ (item₀ < (NeuralLayer.o l₀))) ->
        ((k0 item₀ (NeuralLayer.i l₀) (NeuralLayer.o l₀)))) ∧
      (((k2 (NeuralLayer.o l₀) (NeuralLayer.i l₀) (NeuralLayer.o l₀)))) ∧
      (∀ (a'₄ : Int),
       ((k2 a'₄ (NeuralLayer.i l₀) (NeuralLayer.o l₀))) ->
        (a'₄ = (NeuralLayer.o l₀)))
      
end F
