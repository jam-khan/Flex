import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def WritebackWasm2cMarshalAndWritebackFdstat := 
 ∀ (addr₀ : Int),
  ∀ (ctx₀ : TypesVmCtx),
   (addr₀ ≥ 0) ->
    ∀ (a'₂ : Prop),
     (a'₂ = (((addr₀ ≤ (addr₀ + 24)) ∧ (0 ≤ addr₀)) ∧ ((addr₀ + 24) < (0 + types_LINEAR_MEM_SIZE)))) ->
      a'₂ ->
       ∀ (a'₃ : Int),
        (a'₃ ≥ 0) ->
         ∀ (a'₄ : Int),
          (a'₄ ≥ 0) ->
           ∀ (a'₅ : Int),
            (a'₅ ≥ 0) ->
             (((0 ≤ addr₀)) ∧
             ((2 ≤ (2 + addr₀))) ∧
             (((2 + addr₀) < (0 + types_LINEAR_MEM_SIZE)))
             ) ∧
             (∀ (a'₆ : Int),
              ∀ (a'₇ : Int),
               (a'₇ ≥ 0) ->
                (((a'₆ ≥ 0) ∧ (a'₆ ≤ 65535)) -> (a'₇ = a'₆)) ->
                 (((0 ≤ (addr₀ + 2))) ∧
                 ((2 ≤ (2 + (addr₀ + 2)))) ∧
                 (((2 + (addr₀ + 2)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (((0 ≤ (addr₀ + 8))) ∧
                 ((8 ≤ (8 + (addr₀ + 8)))) ∧
                 (((8 + (addr₀ + 8)) < (0 + types_LINEAR_MEM_SIZE)))
                 ) ∧
                 (((0 ≤ (addr₀ + 16))) ∧
                 ((8 ≤ (8 + (addr₀ + 16)))) ∧
                 (((8 + (addr₀ + 16)) < (0 + types_LINEAR_MEM_SIZE)))
                 )
                 )
             
end F
