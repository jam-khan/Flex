import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__WriteU8 := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (cnt₀ : Int),
   ∀ (v₀ : Int),
    ((0 ≤ cnt₀) ∧ (1 ≤ (1 + cnt₀)) ∧ ((1 + cnt₀) < (0 + types_LINEAR_MEM_SIZE))) ->
     (cnt₀ ≥ 0) ->
      (v₀ ≥ 0) ->
       ((TypesVmCtx.base cx₀) ≥ 0) ->
        (types_LINEAR_MEM_SIZE ≥ 0) ->
         ((TypesVmCtx.arg_buf cx₀) < types_TWO_POWER_20) ->
          ((TypesVmCtx.env_buf cx₀) < types_TWO_POWER_20) ->
           (cnt₀ < types_LINEAR_MEM_SIZE)
end F
