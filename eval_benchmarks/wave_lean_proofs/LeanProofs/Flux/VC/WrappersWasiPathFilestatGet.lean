import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.User.Fun.FlagSet
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
import LeanProofs.Flux.Fun.TypesATSYMLINKNOFOLLOW
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiPathFilestatGet := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, 
 ∀ (ctx₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (flags₀ : Int),
    ∀ (pathname₀ : Int),
     ∀ (path_len₀ : Int),
      (v_fd₀ ≥ 0) ->
       (flags₀ ≥ 0) ->
        (pathname₀ ≥ 0) ->
         (path_len₀ ≥ 0) ->
          ∀ (flags₁ : Int),
           ((TypesVmCtx.base ctx₀) ≥ 0) ->
            (types_LINEAR_MEM_SIZE ≥ 0) ->
             ∀ (a'₆ : TypesFdMap),
              ((TypesVmCtx.arg_buf ctx₀) < types_TWO_POWER_20) ->
               ((TypesVmCtx.env_buf ctx₀) < types_TWO_POWER_20) ->
                ∀ (v₀ : Int),
                 (v₀ < 1024) ->
                  (v₀ ≥ 0) ->
                   ∀ (v₁ : Int),
                    (v₁ < 1024) ->
                     (v₁ ≥ 0) ->
                      (∀ (a'₉ : Int),
                       (v_fd₀ < types_MAX_SBOX_FDS) ->
                        ((k0 a'₉ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ flags₁ (TypesFdMap.reserve_len a'₆) (TypesFdMap.counter a'₆) v₀ v₁))) ∧
                      (∀ (a'₁₀ : Int),
                       ((k0 a'₁₀ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ flags₁ (TypesFdMap.reserve_len a'₆) (TypesFdMap.counter a'₆) v₀ v₁)) ->
                        (¬(v_fd₀ ≠ 3)) ->
                         (¬(v_fd₀ ≠ 3)) ->
                          ∀ (should_follow₀ : Prop),
                           ∀ (a'₁₂ : TcbPathHostPath),
                            (((TcbPathHostPath.depth a'₁₂) ≥ 0) ∧ (TcbPathHostPath.is_relative a'₁₂) ∧ (should_follow₀ -> (TcbPathHostPath.non_symlink a'₁₂)) ∧ (TcbPathHostPath.non_symlink_prefixes a'₁₂)) ->
                             ∀ (n_flags₀ : Int),
                              ∀ (b₀ : Prop),
                               ((b₀ = (flag_set n_flags₀ 256)) ∧ (b₀ -> (n_flags₀ ≠ 0))) ->
                                (b₀ ≠ should_follow₀) ->
                                 ((n_flags₀ = 0) ∨ (¬(flag_set n_flags₀ types_AT_SYMLINK_NOFOLLOW))) ->
                                  (TcbPathHostPath.non_symlink a'₁₂))
                      
end F
