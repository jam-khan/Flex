import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiFdClose := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   (v_fd₀ ≥ 0) ->
    (¬(v_fd₀ ≥ 8)) ->
     ((TypesVmCtx.base dummy₀) ≥ 0) ->
      (types_LINEAR_MEM_SIZE ≥ 0) ->
       ∀ (a'₁ : TypesFdMap),
        ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
         ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
          ∀ (v₀ : Int),
           (v₀ < 1024) ->
            (v₀ ≥ 0) ->
             ∀ (v₁ : Int),
              (v₁ < 1024) ->
               (v₁ ≥ 0) ->
                ((TypesFdMap.counter a'₁) ≥ 0) ->
                 (((0 ≤ v_fd₀)) ∧
                 ((v_fd₀ < types_MAX_SBOX_FDS))
                 ) ∧
                 (((k0 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁))) ∧
                 (∀ (a'₄ : Int),
                  ((k1 a'₄ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁))) ∧
                 (((k0 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁)) ->
                  (∀ (a'₅ : Int),
                   ((k1 a'₅ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁)) ->
                    ((k2 a'₅ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁))) ∧
                  (∀ (a'₆ : Int),
                   ((k2 a'₆ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁)) ->
                    (v_fd₀ < types_MAX_SBOX_FDS))
                  )
                 
end F
