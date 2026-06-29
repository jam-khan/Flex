import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiFdReaddir := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (n₀ : Int),
   ∀ (n₁ : Int),
    ∀ (buf_len₀ : Int),
     ∀ (cookie₀ : Int),
      (n₀ ≥ 0) ->
       (n₁ ≥ 0) ->
        (buf_len₀ ≥ 0) ->
         (cookie₀ ≥ 0) ->
          ((TypesVmCtx.base dummy₀) ≥ 0) ->
           (types_LINEAR_MEM_SIZE ≥ 0) ->
            ∀ (a'₄ : TypesFdMap),
             ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
              ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
               ∀ (v₀ : Int),
                (v₀ < 1024) ->
                 (v₀ ≥ 0) ->
                  ∀ (v₁ : Int),
                   (v₁ < 1024) ->
                    (v₁ ≥ 0) ->
                     (∀ (a'₇ : Int),
                      (n₀ < types_MAX_SBOX_FDS) ->
                       ((k0 a'₇ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) n₀ n₁ buf_len₀ cookie₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁))) ∧
                     (∀ (a'₈ : Int),
                      ((k0 a'₈ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) n₀ n₁ buf_len₀ cookie₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁)) ->
                       (buf_len₀ ≥ buf_len₀))
                     
end F
