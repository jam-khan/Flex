import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiSockRecv := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Prop) -> (a18 : Int) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (ri_data₀ : Int),
    ∀ (ri_data_count₀ : Int),
     ∀ (ri_flags₀ : Int),
      (v_fd₀ ≥ 0) ->
       (ri_data₀ ≥ 0) ->
        (ri_data_count₀ ≥ 0) ->
         (ri_flags₀ ≥ 0) ->
          ((TypesVmCtx.base dummy₀) ≥ 0) ->
           (types_LINEAR_MEM_SIZE ≥ 0) ->
            ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
             ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
              ∀ (a'₄ : TypesFdMap),
               (∀ (a'₅ : Int),
                (v_fd₀ < types_MAX_SBOX_FDS) ->
                 ((k0 a'₅ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄)))) ∧
               (∀ (a'₆ : Int),
                ((k0 a'₆ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄))) ->
                 (((k1 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆))) ∧
                 (((k1 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆)) ->
                  (((k2 0 0 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆))) ∧
                  (∀ (num₀ : Int),
                   ∀ (i₀ : Int),
                    ((k2 num₀ i₀ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆)) ->
                     (i₀ < ri_data_count₀) ->
                      (∀ (a'₉ : Int),
                       ∀ (a'₁₀ : Int),
                        (((k3 a'₉ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀))) ∧
                        (((k4 a'₁₀ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀)))
                        ) ∧
                      (∀ (a'₁₁ : Int),
                       ((k3 a'₁₁ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀)) ->
                        ∀ (a'₁₂ : Int),
                         ((k4 a'₁₂ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀)) ->
                          (a'₁₁ ≥ 0) ->
                           (a'₁₂ ≥ 0) ->
                            ∀ (a'₁₃ : Prop),
                             (a'₁₃ = ((((0 ≤ a'₁₂) ∧ (a'₁₁ ≤ (a'₁₁ + a'₁₂))) ∧ (0 ≤ a'₁₁)) ∧ ((a'₁₁ + a'₁₂) < (0 + types_LINEAR_MEM_SIZE)))) ->
                              a'₁₃ ->
                               ∀ (a'₁₄ : Int),
                                (((0 ≤ a'₁₂)) ∧
                                ((a'₁₁ ≤ (a'₁₁ + a'₁₂))) ∧
                                ((0 ≤ a'₁₁)) ∧
                                (((a'₁₁ + a'₁₂) < (0 + types_LINEAR_MEM_SIZE))) ∧
                                ((a'₁₂ < types_LINEAR_MEM_SIZE))
                                ) ∧
                                (∀ (a'₁₅ : Int),
                                 ((k5 a'₁₅ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀ a'₁₁ a'₁₂ True a'₁₄))) ∧
                                (∀ (a'₁₆ : Int),
                                 ((k5 a'₁₆ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀ a'₁₁ a'₁₂ True a'₁₄)) ->
                                  (a'₁₆ ≥ 0) ->
                                   ∀ (a'₁₇ : Int),
                                    (a'₁₇ ≥ 0) ->
                                     ((a'₁₆ ≤ 4294967295) -> (a'₁₇ = a'₁₆)) ->
                                      ((k2 (num₀ + a'₁₇) (i₀ + 1) (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) v_fd₀ ri_data₀ ri_data_count₀ ri_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆)))
                                )
                      )
                  )
                 )
               
end F
