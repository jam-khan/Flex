import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__1__WrapAdd := 
 ∀ (me₀ : VecDequeVecDeque),
  ∀ (idx₀ : Int),
   ∀ (addend₀ : Int),
    (idx₀ ≥ 0) ->
     (addend₀ ≥ 0) ->
      ∀ (a'₂ : Int),
       (a'₂ ≥ 0) ->
        ∀ (v₀ : Int),
         ((v₀ = (VecDequeVecDeque.cap me₀)) ∧ (vec_deque_pow2 v₀) ∧ (1 ≤ v₀)) ->
          (v₀ ≥ 0) ->
           ∀ (v₁ : Int),
            (v₁ < v₀) ->
             (v₁ ≥ 0) ->
              (v₁ < (VecDequeVecDeque.cap me₀))
end F
