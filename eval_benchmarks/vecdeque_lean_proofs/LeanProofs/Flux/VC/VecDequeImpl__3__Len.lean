import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__3__Len := 
 ∀ (self₀ : VecDequeVecDeque),
  ((VecDequeVecDeque.tail self₀) < (VecDequeVecDeque.cap self₀)) ->
   ((VecDequeVecDeque.tail self₀) ≥ 0) ->
    ((VecDequeVecDeque.head self₀) < (VecDequeVecDeque.cap self₀)) ->
     ((VecDequeVecDeque.head self₀) ≥ 0) ->
      ((vec_deque_pow2 (VecDequeVecDeque.cap self₀)) ∧ (1 ≤ (VecDequeVecDeque.cap self₀))) ->
       ∀ (v₀ : Int),
        ((v₀ = (VecDequeVecDeque.cap self₀)) ∧ (vec_deque_pow2 v₀) ∧ (1 ≤ v₀)) ->
         (v₀ ≥ 0) ->
          ∀ (v₁ : Int),
           (v₁ < v₀) ->
            (v₁ ≥ 0) ->
             (v₁ < (VecDequeVecDeque.cap self₀))
end F
