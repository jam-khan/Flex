import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def UninitFillFromSlice := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (∀ (a'₀ : Int),
    ((k0 a'₀ n₀))) ∧
   (((k1 0 0 n₀ 0 n₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ n₀)) ->
     ((k2 a'₁ 0 0 n₀ 0 n₀))) ∧
   (∀ (i₀ : Int),
    ∀ (iter₀ : SliceIterIter),
     ∀ (a'₄ : Int),
      ((k1 i₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₄ n₀)) ->
       (∀ (a'₅ : Int),
        ((k2 a'₅ i₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₄ n₀)) ->
         ((k3 a'₅ n₀ i₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₄))) ∧
       (∀ (next_s₀ : SliceIterIter),
        ((((SliceIterIter.idx iter₀) + 1) = (SliceIterIter.idx next_s₀)) ∧ ((SliceIterIter.len iter₀) = (SliceIterIter.len next_s₀))) ->
         ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = False) ->
          (a'₄ = n₀)) ∧
         ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = True) ->
          ∀ (a'₇ : Int),
           ((k3 a'₇ n₀ i₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₄)) ->
            ((a'₄ < n₀)) ∧
            (((k1 (i₀ + 1) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) (a'₄ + 1) n₀))) ∧
            (∀ (a'₈ : Int),
             ((k3 a'₈ n₀ i₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) a'₄)) ->
              ((k2 a'₈ (i₀ + 1) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) (a'₄ + 1) n₀)))
            )
         )
       )
   
end F
