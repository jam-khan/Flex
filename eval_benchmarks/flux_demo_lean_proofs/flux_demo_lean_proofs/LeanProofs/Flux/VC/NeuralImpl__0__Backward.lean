import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.NeuralLayer
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralImpl__0__Backward := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, 
 ∀ (l₀ : NeuralLayer),
  (0 ≤ (NeuralLayer.i l₀)) ->
   (0 ≤ (NeuralLayer.o l₀)) ->
    ((NeuralLayer.i l₀) ≥ 0) ->
     ((NeuralLayer.o l₀) ≥ 0) ->
      (((k0 0 (NeuralLayer.o l₀) (NeuralLayer.i l₀) (NeuralLayer.o l₀)))) ∧
      (∀ (iter₀ : (OpsRangeRange Int)),
       ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (NeuralLayer.i l₀) (NeuralLayer.o l₀))) ->
        ∀ (r₀ : (OpsRangeRange Int)),
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
          (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
           ∀ (a'₂ : Int),
            (a'₂ = (OpsRangeRange.start iter₀)) ->
             (a'₂ ≥ 0) ->
              (((k1 0 (NeuralLayer.i l₀) (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂))) ∧
              (∀ (iter₁ : (OpsRangeRange Int)),
               ((k1 (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂)) ->
                ∀ (r₁ : (OpsRangeRange Int)),
                 ((((OpsRangeRange.start iter₁) < (OpsRangeRange.end_ iter₁)) -> ((OpsRangeRange.start r₁) = ((OpsRangeRange.start iter₁) + 1))) ∧ ((OpsRangeRange.end_ r₁) = (OpsRangeRange.end_ iter₁))) ->
                  ((((OpsRangeRange.start iter₁) < (OpsRangeRange.end_ iter₁)) = False) ->
                   ((a'₂ < (NeuralLayer.o l₀))) ∧
                   ((a'₂ < (NeuralLayer.o l₀))) ∧
                   (((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) (NeuralLayer.i l₀) (NeuralLayer.o l₀))))
                   ) ∧
                  ((((OpsRangeRange.start iter₁) < (OpsRangeRange.end_ iter₁)) = True) ->
                   ∀ (a'₅ : Int),
                    (a'₅ = (OpsRangeRange.start iter₁)) ->
                     (a'₅ ≥ 0) ->
                      ((a'₂ < (NeuralLayer.o l₀))) ∧
                      (∀ (a'₆ : Int),
                       (a'₆ = (NeuralLayer.i l₀)) ->
                        ((k2 a'₆ (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₅))) ∧
                      (∀ (a'₇ : Int),
                       ((k2 a'₇ (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₅)) ->
                        (0 ≤ a'₇) ->
                         ((a'₅ < a'₇)) ∧
                         ((a'₂ < (NeuralLayer.o l₀))) ∧
                         ((a'₅ < (NeuralLayer.i l₀))) ∧
                         ((a'₂ < (NeuralLayer.o l₀))) ∧
                         ((a'₅ < (NeuralLayer.i l₀))) ∧
                         ((a'₂ < (NeuralLayer.o l₀))) ∧
                         (∀ (a'₈ : Int),
                          (a'₈ = (NeuralLayer.i l₀)) ->
                           ((k3 a'₈ (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₅ a'₇))) ∧
                         (∀ (a'₉ : Int),
                          ((k3 a'₉ (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₅ a'₇)) ->
                           (a'₉ = (NeuralLayer.i l₀))) ∧
                         (∀ (a'₁₀ : Int),
                          ((k3 a'₁₀ (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₅ a'₇)) ->
                           ((a'₅ < a'₁₀)) ∧
                           (((k1 (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) (NeuralLayer.i l₀) (NeuralLayer.o l₀) (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₂)))
                           )
                         )
                      )
                  )
              )
      
end F
