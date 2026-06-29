import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__InLinMemUsize := 
 ∀ (ptr₀ : Int),
  ∀ (self₀ : TypesVmCtx),
   (ptr₀ ≥ 0) ->
    ((TypesVmCtx.base self₀) ≥ 0) ->
     (types_LINEAR_MEM_SIZE ≥ 0) ->
      ∀ (a'₁ : TypesFdMap),
       ((TypesVmCtx.arg_buf self₀) < types_TWO_POWER_20) ->
        ((TypesVmCtx.env_buf self₀) < types_TWO_POWER_20) ->
         ∀ (v₀ : Int),
          (v₀ < 1024) ->
           (v₀ ≥ 0) ->
            ∀ (v₁ : Int),
             (v₁ < 1024) ->
              (v₁ ≥ 0) ->
               ((ptr₀ < types_LINEAR_MEM_SIZE) = ((0 ≤ ptr₀) ∧ (ptr₀ < types_LINEAR_MEM_SIZE)))
end F
