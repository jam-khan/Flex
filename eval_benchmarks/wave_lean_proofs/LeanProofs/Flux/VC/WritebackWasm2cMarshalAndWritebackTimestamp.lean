import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def WritebackWasm2cMarshalAndWritebackTimestamp := 
 ∀ (addr₀ : Int),
  ∀ (ctx₀ : TypesVmCtx),
   (addr₀ ≥ 0) ->
    ∀ (a'₂ : Prop),
     (a'₂ = (((addr₀ ≤ (addr₀ + 8)) ∧ (0 ≤ addr₀)) ∧ ((addr₀ + 8) < (0 + types_LINEAR_MEM_SIZE)))) ->
      a'₂ ->
       ∀ (a'₃ : Int),
        (a'₃ ≥ 0) ->
         ((0 ≤ addr₀)) ∧
         ((8 ≤ (8 + addr₀))) ∧
         (((8 + addr₀) < (0 + types_LINEAR_MEM_SIZE)))
         
end F
