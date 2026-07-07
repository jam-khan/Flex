import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def ArraysAverageColor := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (i₀ : Int),
   (n₀ > 0) ->
    (i₀ < 3) ->
     (n₀ ≥ 0) ->
      (i₀ ≥ 0) ->
       (∀ (a'₀ : Int),
        ((k0 a'₀ n₀ i₀))) ∧
       (((k1 0 0 n₀ n₀ i₀))) ∧
       (∀ (a'₁ : Int),
        ((k0 a'₁ n₀ i₀)) ->
         ((k2 a'₁ 0 0 n₀ n₀ i₀))) ∧
       (∀ (sum₀ : Int),
        ∀ (iter₀ : SliceIterIter),
         ((k1 sum₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) n₀ i₀)) ->
          (∀ (a'₄ : Int),
           ((k2 a'₄ sum₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) n₀ i₀)) ->
            ((k3 a'₄ n₀ i₀ sum₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀)))) ∧
          (∀ (next_s₀ : SliceIterIter),
           ((((SliceIterIter.idx iter₀) + 1) = (SliceIterIter.idx next_s₀)) ∧ ((SliceIterIter.len iter₀) = (SliceIterIter.len next_s₀))) ->
            ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = False) ->
             (n₀ ≠ 0)) ∧
            ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = True) ->
             ∀ (a'₆ : Int),
              (a'₆ ≥ 0) ->
               ((k3 a'₆ n₀ i₀ sum₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
                (((k1 (sum₀ + a'₆) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) n₀ i₀))) ∧
                (∀ (a'₇ : Int),
                 ((k3 a'₇ n₀ i₀ sum₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
                  ((k2 a'₇ (sum₀ + a'₆) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) n₀ i₀)))
                )
            )
          )
       
end F
