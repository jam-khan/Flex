import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.NeuralNeuralNetwork
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralImpl__1__Backward := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (i₀ : Int),
  ∀ (o₀ : Int),
   (0 ≤ i₀) ->
    (0 ≤ o₀) ->
     (∀ (i₁ : Int),
      ∀ (o₁ : Int),
       ((NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₀ o₀) = (NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₁ o₁)) ->
        (i₁ ≥ 0) ->
         (o₁ ≥ 0) ->
          (0 ≤ o₁) ->
           (∀ (a'₂ : Int),
            ((k0 a'₂ i₀ o₀ i₁ o₁)) ->
             (a'₂ ≥ 0) ->
              ((a'₂ < o₁)) ∧
              ((a'₂ < o₀))
              ) ∧
           (∀ (item₀ : Int),
            ((0 ≤ item₀) ∧ (item₀ < o₁)) ->
             ((k0 item₀ i₀ o₀ i₁ o₁))) ∧
           (∀ (error₀ : Int),
            (error₀ = (o₁ - 0)) ->
             (0 ≤ error₀) ->
              ((i₀ = i₁)) ∧
              ((error₀ = o₁)) ∧
              ((0 ≤ i₁) ->
               (i₁ = i₀))
              )
           ) ∧
     (∀ (i₂ : Int),
      ∀ (h₀ : Int),
       ∀ (o₂ : Int),
        ((NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₀ o₀) = (NeuralNeuralNetwork.mkNeuralNeuralNetwork₀ i₂ o₂)) ->
         (i₂ ≥ 0) ->
          (h₀ ≥ 0) ->
           (0 ≤ h₀) ->
            ((o₀ = o₂)) ∧
            (((i₀ = i₂)) ∧
            ((0 ≤ i₂) ->
             (i₂ = i₀))
            )
            )
     
end F
