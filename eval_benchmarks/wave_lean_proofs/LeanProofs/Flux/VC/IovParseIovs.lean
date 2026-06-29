import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def IovParseIovs := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, 
 ∀ (ctx₀ : TypesVmCtx),
  ∀ (iovs₀ : Int),
   ∀ (iovcnt₀ : Int),
    (iovs₀ ≥ 0) ->
     (iovcnt₀ ≥ 0) ->
      (((k0 0 0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) iovs₀ iovcnt₀))) ∧
      (∀ (i₀ : Int),
       ∀ (wasm_iovs₀ : Int),
        ((k0 i₀ wasm_iovs₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) iovs₀ iovcnt₀)) ->
         (i₀ < iovcnt₀) ->
          ∀ (a'₅ : Int),
           ∀ (a'₆ : Int),
            (a'₅ ≥ 0) ->
             (a'₆ ≥ 0) ->
              ∀ (a'₇ : Prop),
               (a'₇ = ((((0 ≤ a'₆) ∧ (a'₅ ≤ (a'₅ + a'₆))) ∧ (0 ≤ a'₅)) ∧ ((a'₅ + a'₆) < (0 + types_LINEAR_MEM_SIZE)))) ->
                a'₇ ->
                 ((0 ≤ a'₅)) ∧
                 (((0 ≤ a'₆)) ∧
                 ((a'₅ ≤ (a'₅ + a'₆))) ∧
                 (((a'₅ + a'₆) < types_LINEAR_MEM_SIZE))
                 ) ∧
                 (((k0 (i₀ + 1) (wasm_iovs₀ + 1) (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) iovs₀ iovcnt₀)))
                 )
      
end F
