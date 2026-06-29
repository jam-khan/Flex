import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__1__HandleCapacityIncrease := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (v₀ : VecDequeVecDeque),
  ∀ (old_capacity₀ : Int),
   (((VecDequeVecDeque.tail v₀) < old_capacity₀) ∧ ((2 * old_capacity₀) ≤ (VecDequeVecDeque.cap v₀))) ->
    (old_capacity₀ ≥ 0) ->
     ∀ (new_capacity₀ : Int),
      ((new_capacity₀ = (VecDequeVecDeque.cap v₀)) ∧ (vec_deque_pow2 new_capacity₀) ∧ (1 ≤ new_capacity₀)) ->
       (new_capacity₀ ≥ 0) ->
        ((VecDequeVecDeque.tail v₀) < (VecDequeVecDeque.cap v₀)) ->
         ((VecDequeVecDeque.tail v₀) ≥ 0) ->
          ((VecDequeVecDeque.head v₀) < (VecDequeVecDeque.cap v₀)) ->
           ((VecDequeVecDeque.head v₀) ≥ 0) ->
            ((vec_deque_pow2 (VecDequeVecDeque.cap v₀)) ∧ (1 ≤ (VecDequeVecDeque.cap v₀))) ->
             ((¬((VecDequeVecDeque.tail v₀) ≤ (VecDequeVecDeque.head v₀))) ->
              (((old_capacity₀ - (VecDequeVecDeque.tail v₀)) ≥ 0)) ∧
              ((¬((VecDequeVecDeque.head v₀) < (old_capacity₀ - (VecDequeVecDeque.tail v₀)))) ->
               (((old_capacity₀ - (VecDequeVecDeque.tail v₀)) ≥ 0)) ∧
               (((new_capacity₀ - (old_capacity₀ - (VecDequeVecDeque.tail v₀))) ≥ 0)) ∧
               (((old_capacity₀ - (VecDequeVecDeque.tail v₀)) ≥ 0)) ∧
               ((((new_capacity₀ - (old_capacity₀ - (VecDequeVecDeque.tail v₀))) + (old_capacity₀ - (VecDequeVecDeque.tail v₀))) ≤ (VecDequeVecDeque.cap v₀))) ∧
               ((((VecDequeVecDeque.tail v₀) + (old_capacity₀ - (VecDequeVecDeque.tail v₀))) ≤ (VecDequeVecDeque.cap v₀))) ∧
               ((((VecDequeVecDeque.head v₀) < (new_capacity₀ - (old_capacity₀ - (VecDequeVecDeque.tail v₀)))) ->
                ((k0 (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀))) ∧
               (((k0 (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀)) ->
                ((k1 (new_capacity₀ - (old_capacity₀ - (VecDequeVecDeque.tail v₀))) (VecDequeVecDeque.head v₀) (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀)))
               )
               ) ∧
              (((VecDequeVecDeque.head v₀) < (old_capacity₀ - (VecDequeVecDeque.tail v₀))) ->
               (((old_capacity₀ + (VecDequeVecDeque.head v₀)) ≤ (VecDequeVecDeque.cap v₀))) ∧
               (((0 + (VecDequeVecDeque.head v₀)) ≤ (VecDequeVecDeque.cap v₀))) ∧
               (((((VecDequeVecDeque.head v₀) + old_capacity₀) > (VecDequeVecDeque.tail v₀)) ->
                ((k2 (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀))) ∧
               (((k2 (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀)) ->
                ((k1 (VecDequeVecDeque.tail v₀) ((VecDequeVecDeque.head v₀) + old_capacity₀) (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀)))
               )
               )
              ) ∧
             (((VecDequeVecDeque.tail v₀) ≤ (VecDequeVecDeque.head v₀)) ->
              ((k1 (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.head v₀) (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀))) ∧
             (∀ (a'₁ : Int),
              ∀ (a'₂ : Int),
               ((k1 a'₁ a'₂ (VecDequeVecDeque.head v₀) (VecDequeVecDeque.tail v₀) (VecDequeVecDeque.cap v₀) old_capacity₀ new_capacity₀)) ->
                ((a'₁ < (VecDequeVecDeque.cap v₀))) ∧
                ((a'₂ < (VecDequeVecDeque.cap v₀))) ∧
                (∀ (v₁ : Int),
                 ((v₁ = (VecDequeVecDeque.cap v₀)) ∧ (vec_deque_pow2 v₁) ∧ (1 ≤ v₁)) ->
                  (v₁ ≥ 0) ->
                   (((a'₂ < v₁) = True)) ∧
                   ((a'₁ < (VecDequeVecDeque.cap v₀)) ->
                    (a'₁ ≥ 0) ->
                     (a'₂ < (VecDequeVecDeque.cap v₀)) ->
                      (a'₂ ≥ 0) ->
                       ∀ (v₂ : Int),
                        ((v₂ = (VecDequeVecDeque.cap v₀)) ∧ (vec_deque_pow2 v₂) ∧ (1 ≤ v₂)) ->
                         (v₂ ≥ 0) ->
                          ((a'₁ < v₂) = True))
                   )
                )
             
end F
