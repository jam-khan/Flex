import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def TypesImpl__32__Write := 
 ∀ (ptr₀ : Int),
  ∀ (ctx₀ : TypesVmCtx),
   (ptr₀ ≥ 0) ->
    ∀ (a'₂ : Prop),
     (a'₂ = (((ptr₀ ≤ (ptr₀ + 32)) ∧ (0 ≤ ptr₀)) ∧ ((ptr₀ + 32) < (0 + types_LINEAR_MEM_SIZE)))) ->
      a'₂ ->
       ∀ (a'₃ : Prop),
        a'₃ ->
         ∀ (a'₄ : Int),
          (a'₄ ≥ 0) ->
           (((0 ≤ ptr₀)) ∧
           ((8 ≤ (8 + ptr₀))) ∧
           (((8 + ptr₀) < (0 + types_LINEAR_MEM_SIZE)))
           ) ∧
           (∀ (a'₅ : Int),
            (a'₅ ≥ 0) ->
             (((0 ≤ (ptr₀ + 8))) ∧
             ((2 ≤ (2 + (ptr₀ + 8)))) ∧
             (((2 + (ptr₀ + 8)) < (0 + types_LINEAR_MEM_SIZE)))
             ) ∧
             (∀ (a'₆ : Int),
              (a'₆ ≥ 0) ->
               (((0 ≤ (ptr₀ + 10))) ∧
               ((2 ≤ (2 + (ptr₀ + 10)))) ∧
               (((2 + (ptr₀ + 10)) < (0 + types_LINEAR_MEM_SIZE)))
               ) ∧
               (∀ (a'₇ : Int),
                (a'₇ ≥ 0) ->
                 (((0 ≤ (ptr₀ + 16))) ∧
                 ((8 ≤ (8 + (ptr₀ + 16)))) ∧
                 (((8 + (ptr₀ + 16)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (∀ (a'₈ : Int),
                  (a'₈ ≥ 0) ->
                   ((0 ≤ (ptr₀ + 24))) ∧
                   ((2 ≤ (2 + (ptr₀ + 24)))) ∧
                   (((2 + (ptr₀ + 24)) < (0 + types_LINEAR_MEM_SIZE)))
                   )
                 )
               )
             )
           
end F
