import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__CopyArgBufferToSandbox := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (n₀ : Int),
   ∀ (n₁ : Int),
    (n₁ ≥ 0) ->
     (n₀ ≥ 0) ->
      ((TypesVmCtx.arg_buf cx₀) = n₀) ->
       ∀ (a'₁ : Prop),
        (a'₁ = ((((0 ≤ n₀) ∧ (n₁ ≤ (n₁ + n₀))) ∧ (0 ≤ n₁)) ∧ ((n₁ + n₀) < (0 + types_LINEAR_MEM_SIZE)))) ->
         a'₁ ->
          ((TypesVmCtx.base cx₀) ≥ 0) ->
           (types_LINEAR_MEM_SIZE ≥ 0) ->
            ((TypesVmCtx.arg_buf cx₀) < types_TWO_POWER_20) ->
             ((TypesVmCtx.env_buf cx₀) < types_TWO_POWER_20) ->
              (((n₁ + n₀) < types_LINEAR_MEM_SIZE)) ∧
              ((n₀ ≤ (TypesVmCtx.arg_buf cx₀)))
              
end F
