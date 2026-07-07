import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.NeuralNeuralNetwork
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralImpl__1__New := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (input_size₀ : Int),
  ∀ (output_size₀ : Int),
   ∀ (a'₀ : Int),
    (input_size₀ ≥ 0) ->
     (a'₀ ≥ 0) ->
      (output_size₀ ≥ 0) ->
       (a'₀ ≠ 0) ->
        ((0 < a'₀)) ∧
        ((0 < a'₀) ->
         ∀ (hidden_sizes_elem₀ : Int),
          (hidden_sizes_elem₀ ≥ 0) ->
           ∀ (a'₂ : Int),
            (a'₂ ≥ 0) ->
             (((k0 hidden_sizes_elem₀ output_size₀ input_size₀ output_size₀ a'₀ hidden_sizes_elem₀ a'₂))) ∧
             (∀ (a'₃ : NeuralNeuralNetwork),
              ((k0 (NeuralNeuralNetwork.i a'₃) (NeuralNeuralNetwork.o a'₃) input_size₀ output_size₀ a'₀ hidden_sizes_elem₀ a'₂)) ->
               (((NeuralNeuralNetwork.i a'₃) = hidden_sizes_elem₀)) ∧
               (((NeuralNeuralNetwork.o a'₃) = output_size₀))
               )
             )
        
end F
