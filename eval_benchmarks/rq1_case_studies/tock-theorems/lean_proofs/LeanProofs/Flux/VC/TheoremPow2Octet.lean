import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Octet
import LeanProofs.Flux.Fun.Pow2
open Classical
set_option linter.unusedVariables false


namespace F



def TheoremPow2Octet := 
 ∀ (r₀ : Int),
  ((pow2 r₀) ∧ (r₀ ≥ 8)) ->
   (r₀ ≥ 0) ->
    (r₀ ≤ 4294967295) ->
     (octet r₀)
end F
