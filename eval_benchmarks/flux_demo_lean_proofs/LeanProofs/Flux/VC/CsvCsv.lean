import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def CsvCsv := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (constgen_N_0 : Int),
  ∀ (a'₀ : Int),
   (a'₀ ≥ 0) ->
    (0 ≤ constgen_N_0) ->
     (((k0 0 0 a'₀ constgen_N_0 a'₀))) ∧
     (∀ (row_vals₀ : Int),
      ∀ (iter₀ : SliceIterIter),
       ((k0 row_vals₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) constgen_N_0 a'₀)) ->
        ∀ (next_s₀ : SliceIterIter),
         ((((SliceIterIter.idx iter₀) + 1) = (SliceIterIter.idx next_s₀)) ∧ ((SliceIterIter.len iter₀) = (SliceIterIter.len next_s₀))) ->
          ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = False) ->
           ∀ (a'₄ : Int),
            ((k1 a'₄ row_vals₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) constgen_N_0 a'₀)) ->
             (a'₄ = constgen_N_0)) ∧
          ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = True) ->
           (∀ (a'₅ : Int),
            ((k1 a'₅ row_vals₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) constgen_N_0 a'₀)) ->
             ((k2 a'₅ constgen_N_0 a'₀ row_vals₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀)))) ∧
           (((k2 constgen_N_0 constgen_N_0 a'₀ row_vals₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀)))) ∧
           ((0 ≤ (row_vals₀ + 1)) ->
            (((k0 (row_vals₀ + 1) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) constgen_N_0 a'₀))) ∧
            (∀ (a'₆ : Int),
             ((k2 a'₆ constgen_N_0 a'₀ row_vals₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀))) ->
              ((k1 a'₆ (row_vals₀ + 1) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) constgen_N_0 a'₀)))
            )
           )
          )
     
end F
