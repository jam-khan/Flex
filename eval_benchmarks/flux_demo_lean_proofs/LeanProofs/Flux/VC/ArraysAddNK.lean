import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def ArraysAddNK := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (constgen_N_0 : Int),
  ∀ (k₀ : Int),
   (k₀ ≥ 0) ->
    ((¬(k₀ < constgen_N_0)) ->
     ((k0 constgen_N_0 constgen_N_0 k₀))) ∧
    ((k₀ < constgen_N_0) ->
     ((k0 k₀ constgen_N_0 k₀))) ∧
    (∀ (k₁ : Int),
     ((k0 k₁ constgen_N_0 k₀)) ->
      (((k1 0 0 k₁ constgen_N_0 k₀ k₁))) ∧
      (∀ (res₀ : Int),
       ∀ (iter₀ : (OpsRangeRange Int)),
        ((k1 res₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) constgen_N_0 k₀ k₁)) ->
         ∀ (r₀ : (OpsRangeRange Int)),
          ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
           (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
            ∀ (a'₅ : Int),
             (a'₅ = (OpsRangeRange.start iter₀)) ->
              (a'₅ ≥ 0) ->
               (((1 = (0 + 1)) = True)) ∧
               ((a'₅ < constgen_N_0)) ∧
               ((a'₅ < constgen_N_0) ->
                ∀ (arr_elem₀ : Int),
                 ((k1 (res₀ + arr_elem₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) constgen_N_0 k₀ k₁)))
               )
      )
    
end F
