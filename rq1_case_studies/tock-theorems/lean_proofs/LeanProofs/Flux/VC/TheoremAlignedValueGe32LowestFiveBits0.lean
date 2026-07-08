import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Aligned
import LeanProofs.Flux.Fun.Pow2
open Classical
set_option linter.unusedVariables false


namespace F



def TheoremAlignedValueGe32LowestFiveBits0 := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ((y₀ ≥ 32) ∧ (pow2 y₀) ∧ (aligned x₀ y₀)) ->
    (x₀ ≥ 0) ->
     (x₀ ≤ 4294967295) ->
      (y₀ ≥ 0) ->
       (y₀ ≤ 4294967295) ->
        ((BitVec.and (BitVec.ofInt 32 x₀) 31#32) = 0#32)
end F
