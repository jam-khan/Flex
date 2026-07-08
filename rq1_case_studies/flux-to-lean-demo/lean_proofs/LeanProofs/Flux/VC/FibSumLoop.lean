import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibSpecSum
open Classical
set_option linter.unusedVariables false


namespace F



def FibSumLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 0 n₀))) ∧
   (∀ (total₀ : Int),
    ∀ (i₀ : Int),
     ((k0 total₀ i₀ n₀)) ->
      ((¬(i₀ < n₀)) ->
       (total₀ = (fib_spec_sum n₀))) ∧
      ((i₀ < n₀) ->
       ((k0 (total₀ + (i₀ + 1)) (i₀ + 1) n₀)))
      )
   
end F
