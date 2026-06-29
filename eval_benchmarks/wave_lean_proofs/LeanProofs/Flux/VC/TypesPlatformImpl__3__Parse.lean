import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TypesPlatformImpl__3__Parse := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, 
 ∀ (host_buf₀ : Int),
  ∀ (in_idx₀ : Int),
   (in_idx₀ ≥ 0) ->
    (host_buf₀ ≥ 0) ->
     (¬((in_idx₀ + 18) ≥ host_buf₀)) ->
      (((0 ≤ (in_idx₀ + 0))) ∧
      (((in_idx₀ + 0) < host_buf₀))
      ) ∧
      (∀ (a'₂ : Int),
       ((k0 a'₂ host_buf₀ in_idx₀))) ∧
      (∀ (a'₃ : Int),
       ((k0 a'₃ host_buf₀ in_idx₀)) ->
        (a'₃ ≥ 0) ->
         (((0 ≤ (in_idx₀ + 1))) ∧
         (((in_idx₀ + 1) < host_buf₀))
         ) ∧
         (∀ (a'₄ : Int),
          ((k1 a'₄ host_buf₀ in_idx₀ a'₃))) ∧
         (∀ (a'₅ : Int),
          ((k1 a'₅ host_buf₀ in_idx₀ a'₃)) ->
           (a'₅ ≥ 0) ->
            (((0 ≤ (in_idx₀ + 2))) ∧
            (((in_idx₀ + 2) < host_buf₀))
            ) ∧
            (∀ (a'₆ : Int),
             ((k2 a'₆ host_buf₀ in_idx₀ a'₃ a'₅))) ∧
            (∀ (a'₇ : Int),
             ((k2 a'₇ host_buf₀ in_idx₀ a'₃ a'₅)) ->
              (a'₇ ≥ 0) ->
               (((0 ≤ (in_idx₀ + 3))) ∧
               (((in_idx₀ + 3) < host_buf₀))
               ) ∧
               (∀ (a'₈ : Int),
                ((k3 a'₈ host_buf₀ in_idx₀ a'₃ a'₅ a'₇))) ∧
               (∀ (a'₉ : Int),
                ((k3 a'₉ host_buf₀ in_idx₀ a'₃ a'₅ a'₇)) ->
                 (a'₉ ≥ 0) ->
                  (((0 ≤ (in_idx₀ + 4))) ∧
                  (((in_idx₀ + 4) < host_buf₀))
                  ) ∧
                  (∀ (a'₁₀ : Int),
                   ((k4 a'₁₀ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉))) ∧
                  (∀ (a'₁₁ : Int),
                   ((k4 a'₁₁ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉)) ->
                    (a'₁₁ ≥ 0) ->
                     (((0 ≤ (in_idx₀ + 5))) ∧
                     (((in_idx₀ + 5) < host_buf₀))
                     ) ∧
                     (∀ (a'₁₂ : Int),
                      ((k5 a'₁₂ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁))) ∧
                     (∀ (a'₁₃ : Int),
                      ((k5 a'₁₃ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁)) ->
                       (a'₁₃ ≥ 0) ->
                        (((0 ≤ (in_idx₀ + 6))) ∧
                        (((in_idx₀ + 6) < host_buf₀))
                        ) ∧
                        (∀ (a'₁₄ : Int),
                         ((k6 a'₁₄ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃))) ∧
                        (∀ (a'₁₅ : Int),
                         ((k6 a'₁₅ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃)) ->
                          (a'₁₅ ≥ 0) ->
                           (((0 ≤ (in_idx₀ + 7))) ∧
                           (((in_idx₀ + 7) < host_buf₀))
                           ) ∧
                           (∀ (a'₁₆ : Int),
                            ((k7 a'₁₆ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅))) ∧
                           (∀ (a'₁₇ : Int),
                            ((k7 a'₁₇ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅)) ->
                             (a'₁₇ ≥ 0) ->
                              ∀ (d_ino₀ : Int),
                               (d_ino₀ ≥ 0) ->
                                (((0 ≤ (in_idx₀ + 18))) ∧
                                (((in_idx₀ + 18) < host_buf₀))
                                ) ∧
                                (∀ (a'₁₉ : Int),
                                 ((k8 a'₁₉ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅ a'₁₇ d_ino₀))) ∧
                                (∀ (a'₂₀ : Int),
                                 ((k8 a'₂₀ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅ a'₁₇ d_ino₀)) ->
                                  (a'₂₀ ≥ 0) ->
                                   ∀ (d_type₀ : Int),
                                    (d_type₀ ≥ 0) ->
                                     (((0 ≤ (in_idx₀ + 16))) ∧
                                     (((in_idx₀ + 16) < host_buf₀))
                                     ) ∧
                                     (∀ (a'₂₂ : Int),
                                      ((k9 a'₂₂ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅ a'₁₇ d_ino₀ a'₂₀ d_type₀))) ∧
                                     (∀ (a'₂₃ : Int),
                                      ((k9 a'₂₃ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅ a'₁₇ d_ino₀ a'₂₀ d_type₀)) ->
                                       (a'₂₃ ≥ 0) ->
                                        (((0 ≤ (in_idx₀ + 17))) ∧
                                        (((in_idx₀ + 17) < host_buf₀))
                                        ) ∧
                                        (∀ (a'₂₄ : Int),
                                         ((k10 a'₂₄ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅ a'₁₇ d_ino₀ a'₂₀ d_type₀ a'₂₃))) ∧
                                        (∀ (a'₂₅ : Int),
                                         ((k10 a'₂₅ host_buf₀ in_idx₀ a'₃ a'₅ a'₇ a'₉ a'₁₁ a'₁₃ a'₁₅ a'₁₇ d_ino₀ a'₂₀ d_type₀ a'₂₃)) ->
                                          (a'₂₅ ≥ 0) ->
                                           ∀ (d_reclen₀ : Int),
                                            (d_reclen₀ ≥ 0) ->
                                             (¬(d_reclen₀ < 19)) ->
                                              (¬((in_idx₀ + d_reclen₀) > host_buf₀)) ->
                                               ((host_buf₀ ≥ (in_idx₀ + d_reclen₀))) ∧
                                               ((d_reclen₀ ≥ 19))
                                               )
                                        )
                                     )
                                )
                           )
                        )
                     )
                  )
               )
            )
         )
      
end F
