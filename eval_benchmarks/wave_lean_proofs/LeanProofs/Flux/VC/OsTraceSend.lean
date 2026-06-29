import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def OsTraceSend := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (ptr₀ : Int),
   ∀ (cnt₀ : Int),
    ∀ (fd₀ : Int),
     ∀ (flags₀ : Int),
      ((0 ≤ cnt₀) ∧ (ptr₀ ≤ (ptr₀ + cnt₀)) ∧ (0 ≤ ptr₀) ∧ ((ptr₀ + cnt₀) < (0 + types_LINEAR_MEM_SIZE)) ∧ (cnt₀ < types_LINEAR_MEM_SIZE)) ->
       (ptr₀ ≥ 0) ->
        (cnt₀ ≥ 0) ->
         ((((TypesVmCtx.base cx₀) + ptr₀) ≤ (((TypesVmCtx.base cx₀) + ptr₀) + cnt₀)) ∧ ((TypesVmCtx.base cx₀) ≤ ((TypesVmCtx.base cx₀) + ptr₀)) ∧ ((((TypesVmCtx.base cx₀) + ptr₀) + cnt₀) < ((TypesVmCtx.base cx₀) + types_LINEAR_MEM_SIZE))) ->
          (fd₀ ≥ 0) ->
           (cnt₀ ≥ cnt₀)
end F
