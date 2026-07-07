import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.NeuralNeuralNetwork
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralImpl__1__Forward := 
 ∀ (i₀ : Int),
  ∀ (o₀ : Int),
   (0 ≤ i₀) ->
    (∀ (i₁ : Int),
     ∀ (o₁ : Int),
      ((NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₀ o₀) = (NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₁ o₁)) ->
       ((i₀ = i₁)) ∧
       ((i₁ ≥ 0) ->
        (o₁ ≥ 0) ->
         (0 ≤ o₁) ->
          (o₁ = o₀))
       ) ∧
    (∀ (i₂ : Int),
     ∀ (h₀ : Int),
      ∀ (o₂ : Int),
       ((NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₀ o₀) = (NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₂ o₂)) ->
        ((i₀ = i₂)) ∧
        ((i₂ ≥ 0) ->
         (h₀ ≥ 0) ->
          (0 ≤ h₀) ->
           (0 ≤ o₂) ->
            (o₂ = o₀))
        )
    
end F
