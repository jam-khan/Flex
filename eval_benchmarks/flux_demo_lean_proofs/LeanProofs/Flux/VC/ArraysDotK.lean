import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def ArraysDotK := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (constgen_N_0 : Int),
  ∀ (k₀ : Int),
   (k₀ ≥ 0) ->
    ((¬(k₀ < constgen_N_0)) ->
     ((k0 constgen_N_0 constgen_N_0 k₀))) ∧
    ((k₀ < constgen_N_0) ->
     ((k0 k₀ constgen_N_0 k₀))) ∧
    (∀ (k₁ : Int),
     ((k0 k₁ constgen_N_0 k₀)) ->
      (((k1 0 k₁ constgen_N_0 k₀ k₁))) ∧
      (∀ (iter₀ : (OpsRangeRange Int)),
       ((k1 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) constgen_N_0 k₀ k₁)) ->
        ∀ (r₀ : (OpsRangeRange Int)),
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
          (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
           ∀ (a'₄ : Int),
            (a'₄ = (OpsRangeRange.start iter₀)) ->
             (a'₄ ≥ 0) ->
              ((a'₄ < constgen_N_0)) ∧
              ((a'₄ < constgen_N_0) ->
               ((k1 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) constgen_N_0 k₀ k₁)))
              )
      )
    
end F
