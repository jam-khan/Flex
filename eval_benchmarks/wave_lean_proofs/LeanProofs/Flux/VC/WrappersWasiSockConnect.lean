import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiSockConnect := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Prop) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> Prop, 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (sockfd₀ : Int),
   ∀ (addr₀ : Int),
    ∀ (addrlen₀ : Int),
     (sockfd₀ ≥ 0) ->
      (addr₀ ≥ 0) ->
       (addrlen₀ ≥ 0) ->
        ((TypesVmCtx.base dummy₀) ≥ 0) ->
         (types_LINEAR_MEM_SIZE ≥ 0) ->
          ((TypesVmCtx.arg_buf dummy₀) < types_TWO_POWER_20) ->
           ((TypesVmCtx.env_buf dummy₀) < types_TWO_POWER_20) ->
            ∀ (a'₃ : TypesFdMap),
             (∀ (a'₄ : Int),
              (sockfd₀ < types_MAX_SBOX_FDS) ->
               ((k0 a'₄ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) sockfd₀ addr₀ addrlen₀ (TypesFdMap.reserve_len a'₃) (TypesFdMap.counter a'₃)))) ∧
             (∀ (a'₅ : Int),
              ((k0 a'₅ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) sockfd₀ addr₀ addrlen₀ (TypesFdMap.reserve_len a'₃) (TypesFdMap.counter a'₃))) ->
               (¬(addrlen₀ ≠ 16)) ->
                ∀ (a'₆ : Prop),
                 (a'₆ = ((((0 ≤ addrlen₀) ∧ (addr₀ ≤ (addr₀ + addrlen₀))) ∧ (0 ≤ addr₀)) ∧ ((addr₀ + addrlen₀) < (0 + types_LINEAR_MEM_SIZE)))) ->
                  a'₆ ->
                   (((0 ≤ addr₀)) ∧
                   ((2 ≤ (2 + addr₀))) ∧
                   (((2 + addr₀) < (0 + types_LINEAR_MEM_SIZE)))
                   ) ∧
                   (∀ (sin_family₀ : Int),
                    (sin_family₀ ≥ 0) ->
                     (((0 ≤ (addr₀ + 2))) ∧
                     ((2 ≤ (2 + (addr₀ + 2)))) ∧
                     (((2 + (addr₀ + 2)) < (0 + types_LINEAR_MEM_SIZE)))
                     ) ∧
                     (∀ (sin_port₀ : Int),
                      (sin_port₀ ≥ 0) ->
                       (((0 ≤ (addr₀ + 4))) ∧
                       ((4 ≤ (4 + (addr₀ + 4)))) ∧
                       (((4 + (addr₀ + 4)) < (0 + types_LINEAR_MEM_SIZE)))
                       ) ∧
                       (∀ (sin_addr_in₀ : Int),
                        (sin_addr_in₀ ≥ 0) ->
                         (∀ (a'₁₀ : Int),
                          ((k1 a'₁₀ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) sockfd₀ addr₀ addrlen₀ (TypesFdMap.reserve_len a'₃) (TypesFdMap.counter a'₃) a'₅ True sin_family₀ sin_port₀ sin_addr_in₀))) ∧
                         (∀ (a'₁₁ : Int),
                          ((k1 a'₁₁ (TypesVmCtx.arg_buf dummy₀) (TypesVmCtx.env_buf dummy₀) (TypesVmCtx.base dummy₀) (TypesVmCtx.homedir_host_fd dummy₀) (TypesVmCtx.net dummy₀) sockfd₀ addr₀ addrlen₀ (TypesFdMap.reserve_len a'₃) (TypesFdMap.counter a'₃) a'₅ True sin_family₀ sin_port₀ sin_addr_in₀)) ->
                           ∀ (a'₁₂ : Int),
                            (a'₁₂ ≥ 0) ->
                             (((a'₁₁ ≥ 0) ∧ (a'₁₁ ≤ 65535)) -> (a'₁₂ = a'₁₁)) ->
                              (a'₅ ≥ 0) ->
                               (¬(a'₅ ≥ 8)) ->
                                ∀ (a'₁₃ : TypesFdMap),
                                 ((TypesFdMap.counter a'₁₃) ≥ 0) ->
                                  ((0 ≤ a'₅)) ∧
                                  ((a'₅ < types_MAX_SBOX_FDS))
                                  )
                         )
                       )
                     )
                   )
             
end F
