import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesAFINET
import LeanProofs.Flux.Fun.TypesSOCKSTREAM
import LeanProofs.Flux.Fun.TypesSOCKDGRAM
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiSocket := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (domain₀ : Int),
   ∀ (ty₀ : Int),
    ∀ (protocol₀ : Int),
     (domain₀ ≥ 0) ->
      (ty₀ ≥ 0) ->
       (protocol₀ ≥ 0) ->
        (¬(protocol₀ ≠ 0)) ->
         ∀ (a'₃ : Int),
          (∀ (a'₄ : Int),
           ((k0 a'₄ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃))) ∧
          (∀ (a'₅ : Int),
           ((k0 a'₅ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃)) ->
            (∀ (a'₆ : Int),
             ((k1 a'₆ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅))) ∧
            (∀ (a'₇ : Int),
             ((k1 a'₇ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅)) ->
              (((k2 True (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅ a'₇))) ∧
              (((k2 False (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅ a'₇))) ∧
              (∀ (a'₈ : Prop),
               ((k2 a'₈ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅ a'₇)) ->
                (¬a'₈) ->
                 (¬(a'₅ ≠ 2)) ->
                  ((a'₇ ≠ 1) ->
                   (¬(a'₇ ≠ 2)) ->
                    ((k3 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅ a'₇ a'₈))) ∧
                  ((¬(a'₇ ≠ 1)) ->
                   ((k3 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅ a'₇ a'₈))) ∧
                  (((k3 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) domain₀ ty₀ protocol₀ a'₃ a'₅ a'₇ a'₈)) ->
                   ((a'₅ = types_AF_INET)) ∧
                   (((a'₇ = types_SOCK_STREAM) ∨ (a'₇ = types_SOCK_DGRAM)))
                   )
                  )
              )
            )
          
end F
