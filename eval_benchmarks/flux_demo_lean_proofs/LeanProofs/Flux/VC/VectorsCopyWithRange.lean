import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsCopyWithRange := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (((k0 0 0 n₀ n₀))) ∧
    (∀ (v₀ : Int),
     ∀ (iter₀ : (OpsRangeRange Int)),
      ((k0 v₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀)) ->
       ∀ (r₀ : (OpsRangeRange Int)),
        ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = False) ->
          (v₀ = n₀)) ∧
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
          ∀ (a'₃ : Int),
           (a'₃ = (OpsRangeRange.start iter₀)) ->
            (a'₃ ≥ 0) ->
             ((a'₃ < n₀)) ∧
             (∀ (a'₄ : Int),
              (0 ≤ (v₀ + 1)) ->
               ((k0 (v₀ + 1) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀)))
             )
         )
    
end F
