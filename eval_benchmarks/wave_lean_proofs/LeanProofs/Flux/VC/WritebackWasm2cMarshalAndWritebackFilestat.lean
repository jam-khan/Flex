import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def WritebackWasm2cMarshalAndWritebackFilestat := 
 ∀ (addr₀ : Int),
  ∀ (ctx₀ : TypesVmCtx),
   (addr₀ ≥ 0) ->
    ∀ (a'₂ : Prop),
     (a'₂ = (((addr₀ ≤ (addr₀ + 64)) ∧ (0 ≤ addr₀)) ∧ ((addr₀ + 64) < (0 + types_LINEAR_MEM_SIZE)))) ->
      a'₂ ->
       ∀ (a'₃ : Int),
        (a'₃ ≥ 0) ->
         ∀ (a'₄ : Int),
          (a'₄ ≥ 0) ->
           ∀ (a'₅ : Int),
            (a'₅ ≥ 0) ->
             ∀ (a'₆ : Int),
              (a'₆ ≥ 0) ->
               (((0 ≤ addr₀)) ∧
               ((8 ≤ (8 + addr₀))) ∧
               (((8 + addr₀) < (0 + types_LINEAR_MEM_SIZE)))
               ) ∧
               (((0 ≤ (addr₀ + 8))) ∧
               ((8 ≤ (8 + (addr₀ + 8)))) ∧
               (((8 + (addr₀ + 8)) < (0 + types_LINEAR_MEM_SIZE)))
               ) ∧
               (∀ (a'₇ : Int),
                (a'₇ ≥ 0) ->
                 (((0 ≤ (addr₀ + 16))) ∧
                 ((8 ≤ (8 + (addr₀ + 16)))) ∧
                 (((8 + (addr₀ + 16)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (((0 ≤ (addr₀ + 24))) ∧
                 ((8 ≤ (8 + (addr₀ + 24)))) ∧
                 (((8 + (addr₀ + 24)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (((0 ≤ (addr₀ + 32))) ∧
                 ((8 ≤ (8 + (addr₀ + 32)))) ∧
                 (((8 + (addr₀ + 32)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (∀ (a'₈ : Int),
                  (a'₈ ≥ 0) ->
                   (((0 ≤ (addr₀ + 40))) ∧
                   ((8 ≤ (8 + (addr₀ + 40)))) ∧
                   (((8 + (addr₀ + 40)) < (0 + types_LINEAR_MEM_SIZE)))
                   ) ∧
                   (∀ (a'₉ : Int),
                    (a'₉ ≥ 0) ->
                     (((0 ≤ (addr₀ + 48))) ∧
                     ((8 ≤ (8 + (addr₀ + 48)))) ∧
                     (((8 + (addr₀ + 48)) < (0 + types_LINEAR_MEM_SIZE)))
                     ) ∧
                     (∀ (a'₁₀ : Int),
                      (a'₁₀ ≥ 0) ->
                       ((0 ≤ (addr₀ + 56))) ∧
                       ((8 ≤ (8 + (addr₀ + 56)))) ∧
                       (((8 + (addr₀ + 56)) < (0 + types_LINEAR_MEM_SIZE)))
                       )
                     )
                   )
                 )
               
end F
