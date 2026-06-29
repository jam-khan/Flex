import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def ArraysDot := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (constgen_N_0 : Int),
  (((k0 0 constgen_N_0 constgen_N_0))) ∧
  (∀ (iter₀ : (OpsRangeRange Int)),
   ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) constgen_N_0)) ->
    ∀ (r₀ : (OpsRangeRange Int)),
     ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
      (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
       ∀ (a'₂ : Int),
        (a'₂ = (OpsRangeRange.start iter₀)) ->
         (a'₂ ≥ 0) ->
          ((a'₂ < constgen_N_0)) ∧
          ((a'₂ < constgen_N_0) ->
           ((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) constgen_N_0)))
          )
  
end F
