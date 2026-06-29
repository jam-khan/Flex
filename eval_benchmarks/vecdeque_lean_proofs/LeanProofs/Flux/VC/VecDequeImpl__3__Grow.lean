import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__3__Grow := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (dummy₀ : VecDequeVecDeque),
  (∀ (a'₀ : Prop),
   a'₀ ->
    ((k0 (VecDequeVecDeque.head dummy₀) (VecDequeVecDeque.tail dummy₀) (VecDequeVecDeque.cap dummy₀)))) ∧
  (((k0 (VecDequeVecDeque.head dummy₀) (VecDequeVecDeque.tail dummy₀) (VecDequeVecDeque.cap dummy₀))) ->
   ∀ (old_cap₀ : Int),
    ((old_cap₀ = (VecDequeVecDeque.cap dummy₀)) ∧ (vec_deque_pow2 old_cap₀) ∧ (1 ≤ old_cap₀)) ->
     (old_cap₀ ≥ 0) ->
      ((VecDequeVecDeque.tail dummy₀) < (VecDequeVecDeque.cap dummy₀)) ->
       ((VecDequeVecDeque.tail dummy₀) ≥ 0) ->
        ((VecDequeVecDeque.head dummy₀) < (VecDequeVecDeque.cap dummy₀)) ->
         ((VecDequeVecDeque.head dummy₀) ≥ 0) ->
          ((vec_deque_pow2 (VecDequeVecDeque.cap dummy₀)) ∧ (1 ≤ (VecDequeVecDeque.cap dummy₀))) ->
           ∀ (v₀ : Prop),
            (vec_deque_pow2 (2 * old_cap₀)) ->
             (((VecDequeVecDeque.tail dummy₀) < (old_cap₀ + old_cap₀))) ∧
             (((VecDequeVecDeque.head dummy₀) < (old_cap₀ + old_cap₀))) ∧
             (((vec_deque_pow2 (old_cap₀ + old_cap₀))) ∧
             ((1 ≤ (old_cap₀ + old_cap₀)))
             ) ∧
             (∀ (new_cap₀ : Int),
              ((new_cap₀ = (old_cap₀ + old_cap₀)) ∧ (vec_deque_pow2 new_cap₀) ∧ (1 ≤ new_cap₀)) ->
               (new_cap₀ ≥ 0) ->
                (((new_cap₀ = (old_cap₀ * 2)) = True)) ∧
                ((((VecDequeVecDeque.tail dummy₀) < old_cap₀)) ∧
                (((2 * old_cap₀) ≤ (old_cap₀ + old_cap₀)))
                )
                )
             )
  
end F
