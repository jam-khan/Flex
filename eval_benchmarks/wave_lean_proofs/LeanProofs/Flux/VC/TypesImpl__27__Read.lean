import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def TypesImpl__27__Read := 
 ∀ (ctx₀ : TypesVmCtx),
  ∀ (ptr₀ : Int),
   (ptr₀ ≥ 0) ->
    ∀ (a'₂ : Prop),
     (a'₂ = (((ptr₀ ≤ (ptr₀ + 48)) ∧ (0 ≤ ptr₀)) ∧ ((ptr₀ + 48) < (0 + types_LINEAR_MEM_SIZE)))) ->
      a'₂ ->
       ∀ (a'₃ : Prop),
        a'₃ ->
         (((0 ≤ ptr₀)) ∧
         ((8 ≤ (8 + ptr₀))) ∧
         (((8 + ptr₀) < (0 + types_LINEAR_MEM_SIZE)))
         ) ∧
         (∀ (userdata₀ : Int),
          (userdata₀ ≥ 0) ->
           (((0 ≤ (ptr₀ + 8))) ∧
           ((8 ≤ (8 + (ptr₀ + 8)))) ∧
           (((8 + (ptr₀ + 8)) < (0 + types_LINEAR_MEM_SIZE)))
           ) ∧
           (∀ (tag₀ : Int),
            (tag₀ ≥ 0) ->
             ((tag₀ = 0) ->
              (((0 ≤ (ptr₀ + 16))) ∧
              ((4 ≤ (4 + (ptr₀ + 16)))) ∧
              (((4 + (ptr₀ + 16)) < (0 + types_LINEAR_MEM_SIZE)))
              ) ∧
              (∀ (v_clock_id₀ : Int),
               (v_clock_id₀ ≥ 0) ->
                (((0 ≤ (ptr₀ + 24))) ∧
                ((8 ≤ (8 + (ptr₀ + 24)))) ∧
                (((8 + (ptr₀ + 24)) < (0 + types_LINEAR_MEM_SIZE)))
                ) ∧
                (∀ (v_timeout₀ : Int),
                 (v_timeout₀ ≥ 0) ->
                  (((0 ≤ (ptr₀ + 32))) ∧
                  ((8 ≤ (8 + (ptr₀ + 32)))) ∧
                  (((8 + (ptr₀ + 32)) < (0 + types_LINEAR_MEM_SIZE)))
                  ) ∧
                  (∀ (v_precision₀ : Int),
                   (v_precision₀ ≥ 0) ->
                    ((0 ≤ (ptr₀ + 40))) ∧
                    ((8 ≤ (8 + (ptr₀ + 40)))) ∧
                    (((8 + (ptr₀ + 40)) < (0 + types_LINEAR_MEM_SIZE)))
                    )
                  )
                )
              ) ∧
             ((tag₀ = 1) ->
              ((0 ≤ (ptr₀ + 16))) ∧
              ((4 ≤ (4 + (ptr₀ + 16)))) ∧
              (((4 + (ptr₀ + 16)) < (0 + types_LINEAR_MEM_SIZE)))
              ) ∧
             ((tag₀ = 2) ->
              ((0 ≤ (ptr₀ + 16))) ∧
              ((4 ≤ (4 + (ptr₀ + 16)))) ∧
              (((4 + (ptr₀ + 16)) < (0 + types_LINEAR_MEM_SIZE)))
              )
             )
           )
         
end F
