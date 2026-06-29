import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsMinIndex := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> Prop, 
 ∀ (k₀ : Int),
  (0 < k₀) ->
   (0 ≤ k₀) ->
    (k₀ ≥ 0) ->
     (((k0 0 0 k₀ k₀))) ∧
     (∀ (min₀ : Int),
      ∀ (iter₀ : (OpsRangeRange Int)),
       ((k0 min₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) k₀)) ->
        ∀ (r₀ : (OpsRangeRange Int)),
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
          ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = False) ->
           (min₀ < k₀)) ∧
          ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
           ∀ (a'₃ : Int),
            (a'₃ = (OpsRangeRange.start iter₀)) ->
             (a'₃ ≥ 0) ->
              ((a'₃ < k₀)) ∧
              ((min₀ < k₀)) ∧
              (∀ (a'₄ : Prop),
               ((¬a'₄) ->
                ((k1 min₀ k₀ min₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₃ a'₄))) ∧
               (a'₄ ->
                ((k1 a'₃ k₀ min₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₃ True))) ∧
               (∀ (min₁ : Int),
                ((k1 min₁ k₀ min₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₃ a'₄)) ->
                 ((k0 min₁ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) k₀)))
               )
              )
          )
     
end F
