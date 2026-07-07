import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def KmeansKmeans := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k11 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k12 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k13 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k14 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k15 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k16 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k17 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k18 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k19 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k20 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k21 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k22 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k23 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k24 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k25 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k26 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k27 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k28 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k29 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k30 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k31 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k32 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k33 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k34 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Prop) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (v₀ : Int),
   ∀ (points₀ : Int),
    (v₀ > 0) ->
     (n₀ ≥ 0) ->
      (0 ≤ v₀) ->
       (0 ≤ points₀) ->
        (((k0 0 100 n₀ v₀ points₀))) ∧
        (∀ (a'₂ : Int),
         (a'₂ = n₀) ->
          ((k1 a'₂ 0 100 n₀ v₀ points₀))) ∧
        (∀ (iter₀ : (OpsRangeRange Int)),
         ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀ v₀ points₀)) ->
          ∀ (r₀ : (OpsRangeRange Int)),
           ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
            (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
             ∀ (a'₅ : Int),
              (a'₅ = (OpsRangeRange.start iter₀)) ->
               (∀ (a'₆ : Int),
                ((k2 a'₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 (0 ≤ a'₆) ->
                  (∀ (a'₇ : Int),
                   ((k1 a'₇ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀ v₀ points₀)) ->
                    (a'₇ = a'₆)) ∧
                  (∀ (v₁ : Int),
                   (v₁ < v₀) ->
                    ∀ (this₀ : Int),
                     (this₀ > 0) ->
                      (v₁ ≥ 0) ->
                       (this₀ ≥ 0) ->
                        (((k3 a'₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                        (((k4 v₁ a'₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                        (((k5 a'₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                        (((k6 a'₆ a'₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                        (((k7 this₀ a'₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                        )
                  ) ∧
               (∀ (a'₁₀ : Int),
                ((k8 a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 (((k2 a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                 (((k3 a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                  ∀ (a'₁₁ : Int),
                   ((k4 a'₁₁ a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                    ((k5 a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                     ∀ (a'₁₂ : Int),
                      ((k6 a'₁₂ a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                       ∀ (a'₁₃ : Int),
                        ((k7 a'₁₃ a'₁₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                         (((k9 a'₁₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                         (((k10 a'₁₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                         (((k11 a'₁₃ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                         )
                 ) ∧
               (∀ (a'₁₄ : Int),
                (a'₁₄ = n₀) ->
                 ((k8 a'₁₄ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               ((∀ (a'₁₅ : Int),
                ((k9 a'₁₅ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ∀ (a'₁₆ : Int),
                  ((k10 a'₁₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                   ∀ (a'₁₇ : Int),
                    ((k11 a'₁₇ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                     (((k12 a'₁₅ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                     (((k13 a'₁₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                     (((k14 a'₁₇ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                     ) ∧
               (∀ (a'₁₈ : Int),
                ∀ (a'₁₉ : Int),
                 ∀ (a'₂₀ : Int),
                  ∀ (a'₂₁ : Int),
                   ((k15 a'₁₈ a'₁₉ a'₂₀ a'₂₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                    (0 ≤ a'₁₈) ->
                     (a'₁₉ ≥ 0) ->
                      (0 ≤ a'₂₀) ->
                       (a'₂₁ ≥ 0) ->
                        ((a'₁₉ > 0)) ∧
                        ((a'₂₁ > 0)) ∧
                        ((a'₂₀ = a'₁₈)) ∧
                        (∀ (this₁ : Int),
                         (this₁ > 0) ->
                          (this₁ ≥ 0) ->
                           (((k16 a'₁₈ a'₁₉ a'₂₀ a'₂₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                           (((k17 a'₁₈ a'₁₈ a'₁₉ a'₂₀ a'₂₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                           (((k18 this₁ a'₁₈ a'₁₉ a'₂₀ a'₂₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                           )
                        ) ∧
               (∀ (a'₂₃ : Int),
                ((k19 a'₂₃ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ∀ (a'₂₄ : Int),
                  ((k20 a'₂₄ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                   ∀ (a'₂₅ : Int),
                    ((k19 a'₂₅ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                     ∀ (a'₂₆ : Int),
                      ((k20 a'₂₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                       (((k15 a'₂₃ a'₂₄ a'₂₅ a'₂₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                       (((k16 a'₂₃ a'₂₄ a'₂₅ a'₂₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                        ∀ (a'₂₇ : Int),
                         ((k17 a'₂₇ a'₂₃ a'₂₄ a'₂₅ a'₂₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                          ∀ (a'₂₈ : Int),
                           ((k18 a'₂₈ a'₂₃ a'₂₄ a'₂₅ a'₂₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                            (((k19 a'₂₇ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                            (((k20 a'₂₈ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                            )
                       ) ∧
               (∀ (a'₂₉ : Int),
                ((k12 a'₂₉ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ((k21 a'₂₉ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (∀ (a'₃₀ : Int),
                ∀ (a'₃₁ : Int),
                 ((k13 a'₃₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                  ∀ (a'₃₂ : Int),
                   ((k14 a'₃₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                    (((k19 a'₃₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                    (((k20 a'₃₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                    ) ∧
               (∀ (a'₃₃ : Int),
                ((k21 a'₃₃ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ((k22 a'₃₃ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (∀ (a'₃₄ : Int),
                ((k19 a'₃₄ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ∀ (a'₃₅ : Int),
                  ((k20 a'₃₅ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                   (((k23 a'₃₄ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                   (((k24 a'₃₅ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                   ) ∧
               (((k25 n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (∀ (a'₃₆ : Int),
                ((k1 a'₃₆ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀ v₀ points₀)) ->
                 ((k26 a'₃₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (∀ (a'₃₇ : Int),
                ((k22 a'₃₇ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ((k27 a'₃₇ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (∀ (a'₃₈ : Int),
                ((k23 a'₃₈ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ∀ (a'₃₉ : Int),
                  ((k24 a'₃₉ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                   (((k28 a'₃₈ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                   (((k29 a'₃₉ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                   ) ∧
               (((k25 n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                (∀ (a'₄₀ : Int),
                 ((k27 a'₄₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                  ((k30 a'₄₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                (∀ (a'₄₁ : Int),
                 ((k28 a'₄₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                  ∀ (a'₄₂ : Int),
                   ((k29 a'₄₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                    (((k31 a'₄₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                    (((k32 a'₄₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                    ) ∧
                (∀ (a'₄₃ : Prop),
                 ((a'₄₃ = False) ->
                  (((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀ v₀ points₀))) ∧
                  (∀ (a'₄₄ : Int),
                   ((k26 a'₄₄ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                    ((k1 a'₄₄ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀ v₀ points₀)))
                  ) ∧
                 ((a'₄₃ = True) ->
                  ∀ (a'₄₅ : Int),
                   ((k30 a'₄₅ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                    ∀ (a'₄₆ : Int),
                     ((k31 a'₄₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                      ∀ (a'₄₇ : Int),
                       ((k32 a'₄₇ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                        (a'₄₅ ≥ 0) ->
                         (0 ≤ a'₄₆) ->
                          (a'₄₇ ≥ 0) ->
                           (((k33 n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅ a'₄₃ a'₄₅ a'₄₆ a'₄₇)) ->
                            (a'₄₇ > 0)) ∧
                           (((k33 n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅ a'₄₃ a'₄₅ a'₄₆ a'₄₇))) ∧
                           (((a'₄₅ < v₀)) ∧
                           (∀ (a'₄₈ : Int),
                            ((k26 a'₄₈ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                             ((k34 a'₄₈ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅ a'₄₃ a'₄₅ a'₄₆ a'₄₇))) ∧
                           (((k34 a'₄₆ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅ a'₄₃ a'₄₅ a'₄₆ a'₄₇))) ∧
                           (∀ (a'₄₉ : Int),
                            ((k34 a'₄₉ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅ a'₄₃ a'₄₅ a'₄₆ a'₄₇)) ->
                             ((k26 a'₄₉ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                           (∀ (a'₅₀ : Int),
                            ((k30 a'₅₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                             ((k27 a'₅₀ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                           (∀ (a'₅₁ : Int),
                            ((k31 a'₅₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                             ∀ (a'₅₂ : Int),
                              ((k32 a'₅₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                               (((k28 a'₅₁ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
                               (((k29 a'₅₂ n₀ v₀ points₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)))
                               )
                           )
                           )
                 )
                )
               )
               )
        
end F
