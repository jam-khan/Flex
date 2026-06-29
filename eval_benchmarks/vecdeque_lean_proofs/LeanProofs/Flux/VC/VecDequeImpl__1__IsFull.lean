import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__1__IsFull := 
 ∀ (a'₀ : VecDequeVecDeque),
  ∀ (v₀ : Int),
   ((v₀ = (VecDequeVecDeque.cap a'₀)) ∧ (vec_deque_pow2 v₀) ∧ (1 ≤ v₀)) ->
    (v₀ ≥ 0) ->
     ∀ (v₁ : Int),
      (v₁ < (VecDequeVecDeque.cap a'₀)) ->
       (v₁ ≥ 0) ->
        ((v₀ - v₁) ≥ 0)
end F
