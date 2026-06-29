import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiFdRenumber := 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (v_from₀ : Int),
   ∀ (v_to₀ : Int),
    (v_from₀ ≥ 0) ->
     (v_to₀ ≥ 0) ->
      (¬(v_from₀ ≥ 8)) ->
       (¬(v_to₀ ≥ 8)) ->
        ((TypesVmCtx.base dummy₀) ≥ 0) ->
         (types_LINEAR_MEM_SIZE ≥ 0) ->
          ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
           ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
            ∀ (a'₂ : TypesFdMap),
             ((v_from₀ < types_MAX_SBOX_FDS)) ∧
             ((v_to₀ < types_MAX_SBOX_FDS))
             
end F
