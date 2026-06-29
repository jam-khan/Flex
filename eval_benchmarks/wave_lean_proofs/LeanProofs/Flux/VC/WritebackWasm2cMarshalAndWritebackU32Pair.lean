import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def WritebackWasm2cMarshalAndWritebackU32Pair := 
 ∀ (addr0₀ : Int),
  ∀ (addr1₀ : Int),
   ∀ (ctx₀ : TypesVmCtx),
    (addr0₀ ≥ 0) ->
     (addr1₀ ≥ 0) ->
      ∀ (a'₃ : Prop),
       (a'₃ = (((addr0₀ ≤ (addr0₀ + 4)) ∧ (0 ≤ addr0₀)) ∧ ((addr0₀ + 4) < (0 + types_LINEAR_MEM_SIZE)))) ->
        a'₃ ->
         ∀ (a'₄ : Prop),
          (a'₄ = (((addr1₀ ≤ (addr1₀ + 4)) ∧ (0 ≤ addr1₀)) ∧ ((addr1₀ + 4) < (0 + types_LINEAR_MEM_SIZE)))) ->
           a'₄ ->
            ∀ (a'₅ : Int),
             ∀ (a'₆ : Int),
              (a'₅ ≥ 0) ->
               (a'₆ ≥ 0) ->
                (((0 ≤ addr0₀)) ∧
                ((4 ≤ (4 + addr0₀))) ∧
                (((4 + addr0₀) < (0 + types_LINEAR_MEM_SIZE)))
                ) ∧
                (((0 ≤ addr1₀)) ∧
                ((4 ≤ (4 + addr1₀))) ∧
                (((4 + addr1₀) < (0 + types_LINEAR_MEM_SIZE)))
                )
                
end F
