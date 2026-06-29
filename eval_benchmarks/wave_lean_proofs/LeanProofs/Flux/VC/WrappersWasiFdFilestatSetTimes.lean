import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiFdFilestatSetTimes := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (v_atim₀ : Int),
    ∀ (v_mtim₀ : Int),
     ∀ (v_fst_flags₀ : Int),
      (v_fd₀ ≥ 0) ->
       (v_atim₀ ≥ 0) ->
        (v_mtim₀ ≥ 0) ->
         (v_fst_flags₀ ≥ 0) ->
          ∀ (a'₄ : Int),
           (a'₄ ≥ 0) ->
            ((v_fst_flags₀ ≤ 65535) -> (a'₄ = v_fst_flags₀)) ->
             (((k0 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ v_atim₀ v_mtim₀ v_fst_flags₀ a'₄))) ∧
             (((k0 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ v_atim₀ v_mtim₀ v_fst_flags₀ a'₄)) ->
              ((TypesVmCtx.base dummy₀) ≥ 0) ->
               (types_LINEAR_MEM_SIZE ≥ 0) ->
                ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
                 ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
                  ∀ (a'₅ : TypesFdMap),
                   (∀ (a'₆ : Int),
                    (v_fd₀ < types_MAX_SBOX_FDS) ->
                     ((k1 a'₆ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ v_atim₀ v_mtim₀ v_fst_flags₀ a'₄ (TypesFdMap.reserve_len a'₅) (TypesFdMap.counter a'₅)))) ∧
                   (∀ (a'₇ : Int),
                    ((k1 a'₇ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ v_atim₀ v_mtim₀ v_fst_flags₀ a'₄ (TypesFdMap.reserve_len a'₅) (TypesFdMap.counter a'₅))) ->
                     ∀ (a'₈ : Prop),
                      ∀ (a'₉ : Prop),
                       ∀ (a'₁₀ : Prop),
                        ∀ (a'₁₁ : Prop),
                         (2 ≤ ((0 + 1) + 1)))
                   )
             
end F
