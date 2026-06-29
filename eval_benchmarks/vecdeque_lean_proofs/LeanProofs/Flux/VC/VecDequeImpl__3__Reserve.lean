import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__3__Reserve := 
 ∀ (me₀ : VecDequeVecDeque),
  ∀ (additional₀ : Int),
   (additional₀ ≥ 0) ->
    ∀ (old_cap₀ : Int),
     ((old_cap₀ = (VecDequeVecDeque.cap me₀)) ∧ (vec_deque_pow2 old_cap₀) ∧ (1 ≤ old_cap₀)) ->
      (old_cap₀ ≥ 0) ->
       ∀ (v₀ : Int),
        (v₀ < (VecDequeVecDeque.cap me₀)) ->
         (v₀ ≥ 0) ->
          ∀ (new_cap₀ : Int),
           ((((v₀ + 1) + additional₀) ≤ new_cap₀) ∧ (vec_deque_pow2 new_cap₀) ∧ ((old_cap₀ < new_cap₀) -> ((2 * old_cap₀) ≤ new_cap₀))) ->
            (new_cap₀ ≥ 0) ->
             (new_cap₀ > old_cap₀) ->
              ((VecDequeVecDeque.tail me₀) < (VecDequeVecDeque.cap me₀)) ->
               ((VecDequeVecDeque.tail me₀) ≥ 0) ->
                ((VecDequeVecDeque.head me₀) < (VecDequeVecDeque.cap me₀)) ->
                 ((VecDequeVecDeque.head me₀) ≥ 0) ->
                  ((vec_deque_pow2 (VecDequeVecDeque.cap me₀)) ∧ (1 ≤ (VecDequeVecDeque.cap me₀))) ->
                   (((new_cap₀ - (v₀ + 1)) ≥ 0)) ∧
                   (((VecDequeVecDeque.tail me₀) < ((v₀ + 1) + (new_cap₀ - (v₀ + 1))))) ∧
                   (((VecDequeVecDeque.head me₀) < ((v₀ + 1) + (new_cap₀ - (v₀ + 1))))) ∧
                   (((vec_deque_pow2 ((v₀ + 1) + (new_cap₀ - (v₀ + 1))))) ∧
                   ((1 ≤ ((v₀ + 1) + (new_cap₀ - (v₀ + 1)))))
                   ) ∧
                   ((((VecDequeVecDeque.tail me₀) < old_cap₀)) ∧
                   (((2 * old_cap₀) ≤ ((v₀ + 1) + (new_cap₀ - (v₀ + 1)))))
                   )
                   
end F
