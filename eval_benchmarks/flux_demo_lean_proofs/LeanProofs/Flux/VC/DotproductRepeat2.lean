import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def DotproductRepeat2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (n₀ ≥ 0) ->
     (((k0 f₀ 0 n₀ n₀ f₀))) ∧
     (∀ (f₁ : Int),
      ∀ (iter₀ : (OpsRangeRange Int)),
       ((k0 f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀ f₀)) ->
        ∀ (r₀ : (OpsRangeRange Int)),
         ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
          (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
           ∀ (a'₄ : Int),
            (a'₄ = (OpsRangeRange.start iter₀)) ->
             (a'₄ ≥ 0) ->
              (∀ (a'₅ : Int),
               ((k1 a'₅ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)) ->
                ∀ (a'₆ : Int),
                 ((k2 a'₆ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)) ->
                  (((0 ≤ a'₆)) ∧
                  ((a'₆ < n₀))
                  ) ∧
                  (∀ (a'₇ : Int),
                   ((k1 a'₇ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)) ->
                    ∀ (a'₈ : Int),
                     ((k2 a'₈ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)) ->
                      (((0 ≤ a'₈)) ∧
                      ((a'₈ < n₀))
                      ) ∧
                      (((k3 n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)))
                      )
                  ) ∧
              (False ->
               ((c0) ∨ False)) ∧
              (((k1 f₁ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄))) ∧
              (((k2 a'₄ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄))) ∧
              (((k3 n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)) ->
               ∀ (a'₉ : Int),
                ((k1 a'₉ n₀ f₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄)) ->
                 ((k0 a'₉ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀ f₀)))
              )
     
end F
