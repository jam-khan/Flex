import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__WriteU64 := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (cnt₀ : Int),
   ∀ (v₀ : Int),
    ((0 ≤ cnt₀) ∧ (8 ≤ (8 + cnt₀)) ∧ ((8 + cnt₀) < (0 + types_LINEAR_MEM_SIZE))) ->
     (cnt₀ ≥ 0) ->
      (v₀ ≥ 0) ->
       ∀ (a'₂ : Int),
        (a'₂ ≥ 0) ->
         (((1 ≤ (1 + cnt₀))) ∧
         (((1 + cnt₀) < (0 + types_LINEAR_MEM_SIZE)))
         ) ∧
         (∀ (a'₃ : Int),
          (a'₃ ≥ 0) ->
           (((0 ≤ (cnt₀ + 1))) ∧
           ((1 ≤ (1 + (cnt₀ + 1)))) ∧
           (((1 + (cnt₀ + 1)) < (0 + types_LINEAR_MEM_SIZE)))
           ) ∧
           (∀ (a'₄ : Int),
            (a'₄ ≥ 0) ->
             (((0 ≤ (cnt₀ + 2))) ∧
             ((1 ≤ (1 + (cnt₀ + 2)))) ∧
             (((1 + (cnt₀ + 2)) < (0 + types_LINEAR_MEM_SIZE)))
             ) ∧
             (∀ (a'₅ : Int),
              (a'₅ ≥ 0) ->
               (((0 ≤ (cnt₀ + 3))) ∧
               ((1 ≤ (1 + (cnt₀ + 3)))) ∧
               (((1 + (cnt₀ + 3)) < (0 + types_LINEAR_MEM_SIZE)))
               ) ∧
               (∀ (a'₆ : Int),
                (a'₆ ≥ 0) ->
                 (((0 ≤ (cnt₀ + 4))) ∧
                 ((1 ≤ (1 + (cnt₀ + 4)))) ∧
                 (((1 + (cnt₀ + 4)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (∀ (a'₇ : Int),
                  (a'₇ ≥ 0) ->
                   (((0 ≤ (cnt₀ + 5))) ∧
                   ((1 ≤ (1 + (cnt₀ + 5)))) ∧
                   (((1 + (cnt₀ + 5)) < (0 + types_LINEAR_MEM_SIZE)))
                   ) ∧
                   (∀ (a'₈ : Int),
                    (a'₈ ≥ 0) ->
                     (((0 ≤ (cnt₀ + 6))) ∧
                     ((1 ≤ (1 + (cnt₀ + 6)))) ∧
                     (((1 + (cnt₀ + 6)) < (0 + types_LINEAR_MEM_SIZE)))
                     ) ∧
                     (∀ (a'₉ : Int),
                      (a'₉ ≥ 0) ->
                       ((0 ≤ (cnt₀ + 7))) ∧
                       ((1 ≤ (1 + (cnt₀ + 7)))) ∧
                       (((1 + (cnt₀ + 7)) < (0 + types_LINEAR_MEM_SIZE)))
                       )
                     )
                   )
                 )
               )
             )
           )
         
end F
