import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiArgsGet := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Prop) -> (a14 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> (a12 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> (a12 : Int) -> (a13 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (argv₀ : Int),
   ∀ (argv_buf₀ : Int),
    (argv₀ ≥ 0) ->
     (argv_buf₀ ≥ 0) ->
      ((TypesVmCtx.base dummy₀) ≥ 0) ->
       (types_LINEAR_MEM_SIZE ≥ 0) ->
        ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
         ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
          ((TypesVmCtx.arg_buf dummy₀) ≥ 0) ->
           (((TypesVmCtx.arg_buf dummy₀) < types_LINEAR_MEM_SIZE)) ∧
           ((((k0 0 0 0 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀))) ∧
           (∀ (idx₀ : Int),
            ∀ (start₀ : Int),
             ∀ (cursor₀ : Int),
              ((k0 idx₀ start₀ cursor₀ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀)) ->
               ((¬(idx₀ < (TypesVmCtx.arg_buf dummy₀))) ->
                ∀ (v₀ : Int),
                 (v₀ ≥ 0) ->
                  (v₀ < 1024) ->
                   ∀ (a'₆ : Prop),
                    (a'₆ = ((((argv₀ + (v₀ * 4)) ≤ ((argv₀ + (v₀ * 4)) + 8)) ∧ (0 ≤ (argv₀ + (v₀ * 4)))) ∧ (((argv₀ + (v₀ * 4)) + 8) < (0 + types_LINEAR_MEM_SIZE)))) ->
                     a'₆ ->
                      ((0 ≤ (argv₀ + (v₀ * 4)))) ∧
                      ((4 ≤ (4 + (argv₀ + (v₀ * 4))))) ∧
                      (((4 + (argv₀ + (v₀ * 4))) < (0 + types_LINEAR_MEM_SIZE)))
                      ) ∧
               ((idx₀ < (TypesVmCtx.arg_buf dummy₀)) ->
                ∀ (a'₇ : Prop),
                 (a'₇ = ((((argv₀ + cursor₀) ≤ ((argv₀ + cursor₀) + 8)) ∧ (0 ≤ (argv₀ + cursor₀))) ∧ (((argv₀ + cursor₀) + 8) < (0 + types_LINEAR_MEM_SIZE)))) ->
                  a'₇ ->
                   ((0 ≤ idx₀)) ∧
                   (∀ (a'₈ : Int),
                    ((k1 a'₈ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True))) ∧
                   (∀ (a'₉ : Int),
                    ((k1 a'₉ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True)) ->
                     (a'₉ ≥ 0) ->
                      ((a'₉ ≠ 0) ->
                       ((k2 idx₀ start₀ cursor₀ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉))) ∧
                      ((¬(a'₉ ≠ 0)) ->
                       (((k3 idx₀ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉))) ∧
                       (∀ (idx₁ : Int),
                        ((k3 idx₁ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉)) ->
                         ((¬(idx₁ < (TypesVmCtx.arg_buf dummy₀))) ->
                          ((k4 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₁))) ∧
                         ((idx₁ < (TypesVmCtx.arg_buf dummy₀)) ->
                          ((0 ≤ idx₁)) ∧
                          (∀ (a'₁₁ : Int),
                           ((k5 a'₁₁ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₁))) ∧
                          (∀ (a'₁₂ : Int),
                           ((k5 a'₁₂ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₁)) ->
                            (a'₁₂ ≥ 0) ->
                             ((a'₁₂ ≠ 0) ->
                              ((k4 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₁))) ∧
                             ((¬(a'₁₂ ≠ 0)) ->
                              ((k3 (idx₁ + 1) (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉)))
                             )
                          ) ∧
                         (((k4 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₁)) ->
                          (((0 ≤ (argv₀ + cursor₀))) ∧
                          ((4 ≤ (4 + (argv₀ + cursor₀)))) ∧
                          (((4 + (argv₀ + cursor₀)) < (0 + types_LINEAR_MEM_SIZE)))
                          ) ∧
                          (∀ (a'₁₃ : Int),
                           (a'₁₃ ≥ 0) ->
                            ((idx₁ ≤ 4294967295) -> (a'₁₃ = idx₁)) ->
                             ((k2 idx₁ a'₁₃ (cursor₀ + 4) (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉)))
                          )
                         )
                       ) ∧
                      (∀ (idx₂ : Int),
                       ∀ (start₁ : Int),
                        ∀ (cursor₁ : Int),
                         ((k2 idx₂ start₁ cursor₁ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉)) ->
                          ((¬((idx₂ + 1) ≥ (TypesVmCtx.arg_buf dummy₀))) ->
                           ((k6 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₂ start₁ cursor₁))) ∧
                          (((idx₂ + 1) ≥ (TypesVmCtx.arg_buf dummy₀)) ->
                           (((0 ≤ (argv₀ + cursor₁))) ∧
                           ((4 ≤ (4 + (argv₀ + cursor₁)))) ∧
                           (((4 + (argv₀ + cursor₁)) < (0 + types_LINEAR_MEM_SIZE)))
                           ) ∧
                           (((k6 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₂ start₁ cursor₁)))
                           ) ∧
                          (((k6 (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀ idx₀ start₀ cursor₀ True a'₉ idx₂ start₁ cursor₁)) ->
                           ((k0 (idx₂ + 1) start₁ cursor₁ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) argv₀ argv_buf₀)))
                          )
                      )
                   )
               )
           )
           
end F
