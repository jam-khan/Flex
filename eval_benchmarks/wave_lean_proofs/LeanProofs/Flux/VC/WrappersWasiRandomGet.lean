import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiRandomGet := 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (ptr₀ : Int),
   ∀ (len₀ : Int),
    (ptr₀ ≥ 0) ->
     (len₀ ≥ 0) ->
      ∀ (a'₂ : Prop),
       (a'₂ = ((((0 ≤ len₀) ∧ (ptr₀ ≤ (ptr₀ + len₀))) ∧ (0 ≤ ptr₀)) ∧ ((ptr₀ + len₀) < (0 + types_LINEAR_MEM_SIZE)))) ->
        a'₂ ->
         ((0 ≤ len₀)) ∧
         ((ptr₀ ≤ (ptr₀ + len₀))) ∧
         ((0 ≤ ptr₀)) ∧
         (((ptr₀ + len₀) < (0 + types_LINEAR_MEM_SIZE))) ∧
         ((len₀ < types_LINEAR_MEM_SIZE))
         
end F
