import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def PollWritebackTimeouts := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Prop) -> (a22 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Prop) -> Prop, 
 ∀ (out_ptr₀ : Int),
  ∀ (timeouts₀ : Int),
   ∀ (ctx₀ : TypesVmCtx),
    (out_ptr₀ ≥ 0) ->
     (((k0 0 0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀)))) ∧
     (∀ (num_events_written₀ : Int),
      ∀ (event_idx₀ : Int),
       ∀ (a'₅ : TypesVmCtx),
        ((k0 num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀))) ->
         (timeouts₀ ≥ 0) ->
          (event_idx₀ < timeouts₀) ->
           ((0 ≤ event_idx₀)) ∧
           (∀ (a'₆ : Int),
            (((k1 a'₆ out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅)))) ∧
            (((k2 out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅))))
            ) ∧
           (∀ (a'₇ : Int),
            ((k1 a'₇ out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅))) ->
             ((k2 out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅))) ->
              (a'₇ ≥ 0) ->
               ∀ (a'₈ : Prop),
                (a'₈ = ((((out_ptr₀ + (num_events_written₀ * 32)) ≤ ((out_ptr₀ + (num_events_written₀ * 32)) + 32)) ∧ (0 ≤ (out_ptr₀ + (num_events_written₀ * 32)))) ∧ (((out_ptr₀ + (num_events_written₀ * 32)) + 32) < (0 + types_LINEAR_MEM_SIZE)))) ->
                 a'₈ ->
                  (∀ (a'₉ : Prop),
                   ((¬a'₉) ->
                    ((k3 num_events_written₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) a'₇ True a'₉))) ∧
                   (a'₉ ->
                    ∀ (a'₁₀ : Int),
                     (a'₁₀ ≥ 0) ->
                      (((num_events_written₀ * 32) ≤ 4294967295) -> (a'₁₀ = (num_events_written₀ * 32))) ->
                       ∀ (ctx₁ : TypesVmCtx),
                        ((k3 (num_events_written₀ + 1) (TypesVmCtx.arg_buf ctx₁) (TypesVmCtx.env_buf ctx₁) (TypesVmCtx.base ctx₁) (TypesVmCtx.homedir_host_fd ctx₁) (TypesVmCtx.net ctx₁) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) a'₇ True True))) ∧
                   (∀ (num_events_written₁ : Int),
                    ∀ (a'₁₃ : TypesVmCtx),
                     ((k3 num_events_written₁ (TypesVmCtx.arg_buf a'₁₃) (TypesVmCtx.env_buf a'₁₃) (TypesVmCtx.base a'₁₃) (TypesVmCtx.homedir_host_fd a'₁₃) (TypesVmCtx.net a'₁₃) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) a'₇ True a'₉)) ->
                      ((k4 num_events_written₁ (TypesVmCtx.arg_buf a'₁₃) (TypesVmCtx.env_buf a'₁₃) (TypesVmCtx.base a'₁₃) (TypesVmCtx.homedir_host_fd a'₁₃) (TypesVmCtx.net a'₁₃) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) a'₇ True)))
                   ) ∧
                  (((k4 num_events_written₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) a'₇ True))) ∧
                  (∀ (num_events_written₂ : Int),
                   ∀ (a'₁₅ : TypesVmCtx),
                    ((k4 num_events_written₂ (TypesVmCtx.arg_buf a'₁₅) (TypesVmCtx.env_buf a'₁₅) (TypesVmCtx.base a'₁₅) (TypesVmCtx.homedir_host_fd a'₁₅) (TypesVmCtx.net a'₁₅) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) num_events_written₀ event_idx₀ (TypesVmCtx.arg_buf a'₅) (TypesVmCtx.env_buf a'₅) (TypesVmCtx.base a'₅) (TypesVmCtx.homedir_host_fd a'₅) (TypesVmCtx.net a'₅) a'₇ True)) ->
                     ((k0 num_events_written₂ (event_idx₀ + 1) (TypesVmCtx.arg_buf a'₁₅) (TypesVmCtx.env_buf a'₁₅) (TypesVmCtx.base a'₁₅) (TypesVmCtx.homedir_host_fd a'₁₅) (TypesVmCtx.net a'₁₅) out_ptr₀ timeouts₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀))))
                  )
           )
     
end F
