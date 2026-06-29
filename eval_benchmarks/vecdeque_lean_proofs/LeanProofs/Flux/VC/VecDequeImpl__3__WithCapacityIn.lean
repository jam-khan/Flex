import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.VecDequePow2
import LeanProofs.Flux.Fun.VecDequeMAXIMUMZSTCAPACITY
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__3__WithCapacityIn := 
 ∀ (capacity₀ : Int),
  ∀ (alloc₀ : Int),
   (capacity₀ < vec_deque_MAXIMUM_ZST_CAPACITY) ->
    (capacity₀ ≥ 0) ->
     (((capacity₀ < 9223372036854775808) = True)) ∧
     (∀ (cap₀ : Int),
      ((capacity₀ ≤ cap₀) ∧ (vec_deque_pow2 cap₀) ∧ (1 ≤ cap₀)) ->
       (cap₀ ≥ 0) ->
        ((0 < cap₀)) ∧
        ((0 < cap₀))
        )
     
end F
