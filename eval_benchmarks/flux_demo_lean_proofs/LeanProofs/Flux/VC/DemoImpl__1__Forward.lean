import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.DemoNeuralNetwork
open Classical
set_option linter.unusedVariables false


namespace F



def DemoImpl__1__Forward := 
 ∀ (i₀ : Int),
  ∀ (o₀ : Int),
   (0 ≤ i₀) ->
    (∀ (i₁ : Int),
     ∀ (o₁ : Int),
      ((DemoNeuralNetwork.mkDemoNeuralNetwork₀ i₀ o₀) = (DemoNeuralNetwork.mkDemoNeuralNetwork₀ i₁ o₁)) ->
       ((i₀ = i₁)) ∧
       ((i₁ ≥ 0) ->
        (o₁ ≥ 0) ->
         (0 ≤ o₁) ->
          (o₁ = o₀))
       ) ∧
    (∀ (i₂ : Int),
     ∀ (h₀ : Int),
      ∀ (o₂ : Int),
       ((DemoNeuralNetwork.mkDemoNeuralNetwork₀ i₀ o₀) = (DemoNeuralNetwork.mkDemoNeuralNetwork₀ i₂ o₂)) ->
        ((i₀ = i₂)) ∧
        ((i₂ ≥ 0) ->
         (h₀ ≥ 0) ->
          (0 ≤ h₀) ->
           (0 ≤ o₂) ->
            (o₂ = o₀))
        )
    
end F
