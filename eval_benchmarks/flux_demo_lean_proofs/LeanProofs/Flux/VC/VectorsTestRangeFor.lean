import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsTestRangeFor := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ ≥ 0) ->
    (hi₀ ≥ 0) ->
     (lo₀ ≤ hi₀) ->
      (((k0 lo₀ hi₀ lo₀ hi₀))) ∧
      (∀ (iter₀ : (OpsRangeRange Int)),
       ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) lo₀ hi₀)) ->
        ∀ (r₀ : (OpsRangeRange Int)),
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
          (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
           ∀ (a'₄ : Int),
            (a'₄ = (OpsRangeRange.start iter₀)) ->
             (a'₄ ≥ 0) ->
              (((lo₀ ≤ a'₄) = True)) ∧
              (((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) lo₀ hi₀)))
              )
      
end F
