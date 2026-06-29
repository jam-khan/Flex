import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiSockSend := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Prop) -> Prop, 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (si_data₀ : Int),
    ∀ (si_data_count₀ : Int),
     ∀ (_si_flags₀ : Int),
      (v_fd₀ ≥ 0) ->
       (si_data₀ ≥ 0) ->
        (si_data_count₀ ≥ 0) ->
         (_si_flags₀ ≥ 0) ->
          ((TypesVmCtx.base cx₀) ≥ 0) ->
           (types_LINEAR_MEM_SIZE ≥ 0) ->
            ((TypesVmCtx.arg_buf cx₀) < types_TWO_POWER_20) ->
             ((TypesVmCtx.env_buf cx₀) < types_TWO_POWER_20) ->
              ∀ (a'₄ : TypesFdMap),
               (∀ (a'₅ : Int),
                (v_fd₀ < types_MAX_SBOX_FDS) ->
                 ((k0 a'₅ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄)))) ∧
               (∀ (a'₆ : Int),
                ((k0 a'₆ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄))) ->
                 (((k1 0 0 (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆))) ∧
                 (∀ (num₀ : Int),
                  ∀ (i₀ : Int),
                   ((k1 num₀ i₀ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆)) ->
                    (i₀ < si_data_count₀) ->
                     (∀ (a'₉ : Int),
                      ∀ (a'₁₀ : Int),
                       (((k2 a'₉ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀))) ∧
                       (((k3 a'₁₀ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀)))
                       ) ∧
                     (∀ (a'₁₁ : Int),
                      ((k2 a'₁₁ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀)) ->
                       ∀ (a'₁₂ : Int),
                        ((k3 a'₁₂ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀)) ->
                         (a'₁₁ ≥ 0) ->
                          (a'₁₂ ≥ 0) ->
                           ∀ (a'₁₃ : Prop),
                            (a'₁₃ = ((((0 ≤ a'₁₂) ∧ (a'₁₁ ≤ (a'₁₁ + a'₁₂))) ∧ (0 ≤ a'₁₁)) ∧ ((a'₁₁ + a'₁₂) < (0 + types_LINEAR_MEM_SIZE)))) ->
                             a'₁₃ ->
                              (((0 ≤ a'₁₂)) ∧
                              ((a'₁₁ ≤ (a'₁₁ + a'₁₂))) ∧
                              ((0 ≤ a'₁₁)) ∧
                              (((a'₁₁ + a'₁₂) < (0 + types_LINEAR_MEM_SIZE))) ∧
                              ((a'₁₂ < types_LINEAR_MEM_SIZE))
                              ) ∧
                              (∀ (a'₁₄ : Int),
                               ((k4 a'₁₄ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀ a'₁₁ a'₁₂ True))) ∧
                              (∀ (a'₁₅ : Int),
                               ((k4 a'₁₅ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆ num₀ i₀ a'₁₁ a'₁₂ True)) ->
                                (a'₁₅ ≥ 0) ->
                                 ∀ (a'₁₆ : Int),
                                  (a'₁₆ ≥ 0) ->
                                   ((a'₁₅ ≤ 4294967295) -> (a'₁₆ = a'₁₅)) ->
                                    ((k1 (num₀ + a'₁₆) (i₀ + 1) (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) v_fd₀ si_data₀ si_data_count₀ _si_flags₀ (TypesFdMap.reserve_len a'₄) (TypesFdMap.counter a'₄) a'₆)))
                              )
                     )
                 )
               
end F
