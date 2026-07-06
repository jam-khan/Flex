import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Aligned
import LeanProofs.Flux.Fun.Pow2
open Classical
set_option linter.unusedVariables false


namespace F



def TheoremPow2LeAligned := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ∀ (z₀ : Int),
    ((aligned x₀ y₀) ∧ (z₀ ≤ y₀) ∧ (pow2 y₀) ∧ (pow2 z₀)) ->
     (x₀ ≥ 0) ->
      (x₀ ≤ 4294967295) ->
       (y₀ ≥ 0) ->
        (y₀ ≤ 4294967295) ->
         (z₀ ≥ 0) ->
          (z₀ ≤ 4294967295) ->
           (aligned x₀ z₀)
end F
