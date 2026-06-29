import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiPathRename := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Prop) -> (a17 : Prop) -> (a18 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> Prop, 
 ∀ (ctx₀ : TypesVmCtx),
  ∀ (v_old_fd₀ : Int),
   ∀ (old_pathname₀ : Int),
    ∀ (old_path_len₀ : Int),
     ∀ (v_new_fd₀ : Int),
      ∀ (new_pathname₀ : Int),
       ∀ (new_path_len₀ : Int),
        (v_old_fd₀ ≥ 0) ->
         (old_pathname₀ ≥ 0) ->
          (old_path_len₀ ≥ 0) ->
           (v_new_fd₀ ≥ 0) ->
            (new_pathname₀ ≥ 0) ->
             (new_path_len₀ ≥ 0) ->
              (¬(v_old_fd₀ ≠ 3)) ->
               ((TypesVmCtx.base ctx₀) ≥ 0) ->
                (types_LINEAR_MEM_SIZE ≥ 0) ->
                 ∀ (a'₇ : TypesFdMap),
                  ((TypesVmCtx.arg_buf ctx₀) < types_TWO_POWER_20) ->
                   ((TypesVmCtx.env_buf ctx₀) < types_TWO_POWER_20) ->
                    ∀ (v₀ : Int),
                     (v₀ < 1024) ->
                      (v₀ ≥ 0) ->
                       ∀ (v₁ : Int),
                        (v₁ < 1024) ->
                         (v₁ ≥ 0) ->
                          ((¬(v_new_fd₀ ≠ 3)) ->
                           (∀ (a'₁₀ : TcbPathHostPath),
                            (((TcbPathHostPath.depth a'₁₀) ≥ 0) ∧ (TcbPathHostPath.is_relative a'₁₀) ∧ (False -> (TcbPathHostPath.non_symlink a'₁₀)) ∧ (TcbPathHostPath.non_symlink_prefixes a'₁₀)) ->
                             (∀ (a'₁₁ : TcbPathHostPath),
                              (((TcbPathHostPath.depth a'₁₁) ≥ 0) ∧ (TcbPathHostPath.is_relative a'₁₁) ∧ (False -> (TcbPathHostPath.non_symlink a'₁₁)) ∧ (TcbPathHostPath.non_symlink_prefixes a'₁₁)) ->
                               ((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁ (TcbPathHostPath.depth a'₁₀) True (TcbPathHostPath.non_symlink a'₁₀) True))) ∧
                             (((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁ (TcbPathHostPath.depth a'₁₀) True (TcbPathHostPath.non_symlink a'₁₀) True))) ∧
                             (((k0 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁ (TcbPathHostPath.depth a'₁₀) True (TcbPathHostPath.non_symlink a'₁₀) True)) ->
                              ((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁)))
                             ) ∧
                           (((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁))) ∧
                           (((k1 (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁)) ->
                            ∀ (a'₁₂ : TypesFdMap),
                             ∀ (v₂ : Int),
                              (v₂ < 1024) ->
                               (v₂ ≥ 0) ->
                                ∀ (v₃ : Int),
                                 (v₃ < 1024) ->
                                  (v₃ ≥ 0) ->
                                   ((k2 (TypesFdMap.reserve_len a'₁₂) (TypesFdMap.counter a'₁₂) v₂ v₃ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁)))
                           ) ∧
                          ((v_new_fd₀ ≠ 3) ->
                           ((k2 (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁))) ∧
                          (∀ (ctx₁ : TypesFdMap),
                           ∀ (ctx₂ : Int),
                            ∀ (ctx₃ : Int),
                             ((k2 (TypesFdMap.reserve_len ctx₁) (TypesFdMap.counter ctx₁) ctx₂ ctx₃ (TypesVmCtx.arg_buf ctx₀) (TypesVmCtx.env_buf ctx₀) (TypesVmCtx.base ctx₀) (TypesVmCtx.homedir_host_fd ctx₀) (TypesVmCtx.net ctx₀) v_old_fd₀ old_pathname₀ old_path_len₀ v_new_fd₀ new_pathname₀ new_path_len₀ (TypesFdMap.reserve_len a'₇) (TypesFdMap.counter a'₇) v₀ v₁)) ->
                              ((ctx₂ < 1024)) ∧
                              ((ctx₃ < 1024))
                              )
                          
end F
