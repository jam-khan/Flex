import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.User.Fun.FlagSet
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesATSYMLINKNOFOLLOW
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiPathFilestatSetTimes := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Prop) -> (a15 : Prop) -> Prop, 
 ∀ (ctx₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (flags₀ : Int),
    ∀ (pathname₀ : Int),
     ∀ (path_len₀ : Int),
      ∀ (atim₀ : Int),
       ∀ (mtim₀ : Int),
        ∀ (v_fst_flags₀ : Int),
         (v_fd₀ ≥ 0) ->
          (flags₀ ≥ 0) ->
           (pathname₀ ≥ 0) ->
            (path_len₀ ≥ 0) ->
             (atim₀ ≥ 0) ->
              (mtim₀ ≥ 0) ->
               (v_fst_flags₀ ≥ 0) ->
                ∀ (a'₈ : Int),
                 (a'₈ ≥ 0) ->
                  ((v_fst_flags₀ ≤ 65535) -> (a'₈ = v_fst_flags₀)) ->
                   (((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈))) ∧
                   (((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈)) ->
                    ∀ (flags₁ : Int),
                     ∀ (a'₁₀ : Prop),
                      ((¬a'₁₀) ->
                       ((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈ flags₁ a'₁₀))) ∧
                      (a'₁₀ ->
                       ∀ (a'₁₁ : Prop),
                        (¬a'₁₁) ->
                         ((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈ flags₁ True))) ∧
                      (((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈ flags₁ a'₁₀)) ->
                       ∀ (a'₁₂ : Prop),
                        ((¬a'₁₂) ->
                         ((k2 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈ flags₁ a'₁₀ a'₁₂))) ∧
                        (a'₁₂ ->
                         ∀ (a'₁₃ : Prop),
                          (¬a'₁₃) ->
                           ((k2 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈ flags₁ a'₁₀ True))) ∧
                        (((k2 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_fd₀ flags₀ pathname₀ path_len₀ atim₀ mtim₀ v_fst_flags₀ a'₈ flags₁ a'₁₀ a'₁₂)) ->
                         (¬(v_fd₀ ≠ 3)) ->
                          (¬(v_fd₀ ≠ 3)) ->
                           ((TypesVmCtx.base ctx₀) ≥ 0) ->
                            (types_LINEAR_MEM_SIZE ≥ 0) ->
                             ∀ (a'₁₄ : TypesFdMap),
                              ((TypesVmCtx.arg_buf ctx₀) < types_TWO_POWER_20) ->
                               ((TypesVmCtx.env_buf ctx₀) < types_TWO_POWER_20) ->
                                ∀ (v₀ : Int),
                                 (v₀ < 1024) ->
                                  (v₀ ≥ 0) ->
                                   ∀ (v₁ : Int),
                                    (v₁ < 1024) ->
                                     (v₁ ≥ 0) ->
                                      ∀ (should_follow₀ : Prop),
                                       ∀ (a'₁₈ : TcbPathHostPath),
                                        (((TcbPathHostPath.depth a'₁₈) ≥ 0) ∧ (TcbPathHostPath.is_relative a'₁₈) ∧ (should_follow₀ -> (TcbPathHostPath.non_symlink a'₁₈)) ∧ (TcbPathHostPath.non_symlink_prefixes a'₁₈)) ->
                                         ∀ (a'₁₉ : Prop),
                                          ∀ (a'₂₀ : Prop),
                                           ∀ (a'₂₁ : Prop),
                                            ∀ (a'₂₂ : Prop),
                                             ∀ (n_flags₀ : Int),
                                              ∀ (b₀ : Prop),
                                               ((b₀ = (flag_set n_flags₀ 256)) ∧ (b₀ -> (n_flags₀ ≠ 0))) ->
                                                (b₀ ≠ should_follow₀) ->
                                                 ((¬(flag_set n_flags₀ types_AT_SYMLINK_NOFOLLOW)) ->
                                                  (TcbPathHostPath.non_symlink a'₁₈)) ∧
                                                 ((2 ≤ ((0 + 1) + 1)))
                                                 )
                        )
                      )
                   
end F
