import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def CsvCsvOpt := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (N₀ : Int),
  ∀ (a'₀ : Int),
   (N₀ ≥ 0) ->
    (a'₀ ≥ 0) ->
     (∀ (a'₁ : Int),
      ((k0 a'₁ N₀ a'₀))) ∧
     (((k1 0 a'₀ N₀ a'₀))) ∧
     (∀ (a'₂ : Int),
      ((k0 a'₂ N₀ a'₀)) ->
       ((k2 a'₂ 0 a'₀ N₀ a'₀))) ∧
     (∀ (iter₀ : SliceIterIter),
      ((k1 (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) N₀ a'₀)) ->
       (∀ (a'₄ : Int),
        ((k2 a'₄ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) N₀ a'₀)) ->
         ((k3 a'₄ N₀ a'₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀)))) ∧
       (∀ (next_s₀ : SliceIterIter),
        ((((SliceIterIter.idx iter₀) + 1) = (SliceIterIter.idx next_s₀)) ∧ ((SliceIterIter.len iter₀) = (SliceIterIter.len next_s₀))) ->
         ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = False) ->
          (((k4 N₀ N₀ a'₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀)))) ∧
          (∀ (a'₆ : Int),
           ((k4 a'₆ N₀ a'₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀))) ->
            (a'₆ = N₀))
          ) ∧
         ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = True) ->
          ∀ (a'₇ : Int),
           ((k3 a'₇ N₀ a'₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
            (a'₇ ≥ 0) ->
             (¬(a'₇ ≠ N₀)) ->
              ((a'₇ = N₀)) ∧
              (((k1 (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) N₀ a'₀))) ∧
              (∀ (a'₈ : Int),
               ((k3 a'₈ N₀ a'₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
                ((k2 a'₈ (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) N₀ a'₀)))
              )
         )
       )
     
end F
