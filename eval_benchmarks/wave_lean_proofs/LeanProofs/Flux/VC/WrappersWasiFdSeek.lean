import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiFdSeek := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> Prop, 
 ∀ (ctx₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (v_filedelta₀ : Int),
    ∀ (v_whence₀ : Int),
     (v_fd₀ ≥ 0) ->
      (v_whence₀ ≥ 0) ->
       (((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀))) ∧
       (((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀)) ->
        ((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀))) ∧
       (((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀)) ->
        ((TypesVmCtx.base ctx₀) ≥ 0) ->
         (types_LINEAR_MEM_SIZE ≥ 0) ->
          ∀ (a'₄ : TypesFdMap),
           ((TypesVmCtx.arg_buf ctx₀) < types_TWO_POWER_20) ->
            ((TypesVmCtx.env_buf ctx₀) < types_TWO_POWER_20) ->
             ∀ (v₀ : Int),
              (v₀ < 1024) ->
               (v₀ ≥ 0) ->
                ∀ (v₁ : Int),
                 (v₁ < 1024) ->
                  (v₁ ≥ 0) ->
                   (∀ (a'₇ : Int),
                    (v_fd₀ < types_MAX_SBOX_FDS) ->
                     ((k2 a'₇ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁))) ∧
                   (∀ (a'₈ : Int),
                    ((k2 a'₈ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁)) ->
                     ∀ (a'₉ : Int),
                      ∀ (a'₁₀ : TypesFdMap),
                       ∀ (v₂ : Int),
                        (v₂ < 1024) ->
                         (v₂ ≥ 0) ->
                          ∀ (v₃ : Int),
                           (v₃ < 1024) ->
                            (v₃ ≥ 0) ->
                             ((k3 (TypesFdMap.reserve_len a'₁₀) (TypesFdMap.counter a'₁₀) v₂ v₃ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁))) ∧
                   (((k3 (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁))) ∧
                   (∀ (ctx₁ : TypesFdMap),
                    ∀ (ctx₂ : Int),
                     ∀ (ctx₃ : Int),
                      ((k3 (TypesFdMap.reserve_len ctx₁) (TypesFdMap.counter ctx₁) ctx₂ ctx₃ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ v_filedelta₀ v_whence₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) v₀ v₁)) ->
                       ((ctx₂ < 1024)) ∧
                       ((ctx₃ < 1024))
                       )
                   )
       
end F
