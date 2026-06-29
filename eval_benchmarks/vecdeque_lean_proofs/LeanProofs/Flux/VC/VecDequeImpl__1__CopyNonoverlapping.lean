import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.VecDequeVecDeque
import LeanProofs.User.Fun.VecDequePow2
open Classical
set_option linter.unusedVariables false


namespace F



def VecDequeImpl__1__CopyNonoverlapping := 
 ∀ (me₀ : VecDequeVecDeque),
  ∀ (dst₀ : Int),
   ∀ (src₀ : Int),
    ∀ (len₀ : Int),
     ((dst₀ + len₀) ≤ (VecDequeVecDeque.cap me₀)) ->
      ((src₀ + len₀) ≤ (VecDequeVecDeque.cap me₀)) ->
       (dst₀ ≥ 0) ->
        (src₀ ≥ 0) ->
         (len₀ ≥ 0) ->
          ∀ (v₀ : Int),
           ((v₀ = (VecDequeVecDeque.cap me₀)) ∧ (vec_deque_pow2 v₀) ∧ (1 ≤ v₀)) ->
            (v₀ ≥ 0) ->
             ((((dst₀ + len₀) ≤ v₀) = True)) ∧
             (∀ (v₁ : Int),
              ((v₁ = (VecDequeVecDeque.cap me₀)) ∧ (vec_deque_pow2 v₁) ∧ (1 ≤ v₁)) ->
               (v₁ ≥ 0) ->
                (((src₀ + len₀) ≤ v₁) = True))
             
end F
