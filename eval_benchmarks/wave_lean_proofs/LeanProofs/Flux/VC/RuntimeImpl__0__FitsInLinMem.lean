import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__FitsInLinMem := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, 
 ∀ (buf₀ : Int),
  ∀ (cnt₀ : Int),
   ∀ (self₀ : TypesVmCtx),
    (buf₀ ≥ 0) ->
     (cnt₀ ≥ 0) ->
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
                 ((¬((buf₀ + cnt₀) ≥ types_LINEAR_MEM_SIZE)) ->
                  ((¬((0 ≤ buf₀) ∧ (buf₀ < types_LINEAR_MEM_SIZE))) ->
                   ((k0 buf₀ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁))) ∧
                  (((0 ≤ buf₀) ∧ (buf₀ < types_LINEAR_MEM_SIZE)) ->
                   ((¬((0 ≤ cnt₀) ∧ (cnt₀ < types_LINEAR_MEM_SIZE))) ->
                    ((k0 buf₀ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁))) ∧
                   (((0 ≤ cnt₀) ∧ (cnt₀ < types_LINEAR_MEM_SIZE)) ->
                    ((k1 (buf₀ ≤ (buf₀ + cnt₀)) buf₀ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁)))
                   ) ∧
                  (((k0 buf₀ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁)) ->
                   ((k1 False buf₀ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁))) ∧
                  (∀ (a'₄ : Prop),
                   ((k1 a'₄ buf₀ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₁) (TypesFdMap.counter a'₁) v₀ v₁)) ->
                    ∀ (a'₅ : TypesFdMap),
                     ∀ (v₂ : Int),
                      (v₂ < 1024) ->
                       (v₂ ≥ 0) ->
                        ∀ (v₃ : Int),
                         (v₃ < 1024) ->
                          (v₃ ≥ 0) ->
                           (a'₄ = ((((0 ≤ cnt₀) ∧ (buf₀ ≤ (buf₀ + cnt₀))) ∧ (0 ≤ buf₀)) ∧ ((buf₀ + cnt₀) < (0 + types_LINEAR_MEM_SIZE)))))
                  ) ∧
                 (((buf₀ + cnt₀) ≥ types_LINEAR_MEM_SIZE) ->
                  (False = ((((0 ≤ cnt₀) ∧ (buf₀ ≤ (buf₀ + cnt₀))) ∧ (0 ≤ buf₀)) ∧ ((buf₀ + cnt₀) < (0 + types_LINEAR_MEM_SIZE)))))
                 
end F
