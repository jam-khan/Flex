import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.User.Fun.FlagSet
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
import LeanProofs.Flux.Fun.TypesONOFOLLOW
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiPathOpen := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (v_dir_fd₀ : Int),
   ∀ (dirflags₀ : Int),
    ∀ (pathname₀ : Int),
     ∀ (path_len₀ : Int),
      ∀ (oflags₀ : Int),
       ∀ (fdflags₀ : Int),
        (v_dir_fd₀ ≥ 0) ->
         (dirflags₀ ≥ 0) ->
          (pathname₀ ≥ 0) ->
           (path_len₀ ≥ 0) ->
            (oflags₀ ≥ 0) ->
             ∀ (dirflags₁ : Int),
              ∀ (should_follow₀ : Prop),
               (¬(v_dir_fd₀ ≠ 3)) ->
                ((TypesVmCtx.base cx₀) ≥ 0) ->
                 (types_LINEAR_MEM_SIZE ≥ 0) ->
                  ∀ (a'₈ : TypesFdMap),
                   ((TypesVmCtx.arg_buf cx₀) < types_TWO_POWER_20) ->
                    ((TypesVmCtx.env_buf cx₀) < types_TWO_POWER_20) ->
                     ∀ (v₀ : Int),
                      (v₀ < 1024) ->
                       (v₀ ≥ 0) ->
                        ∀ (v₁ : Int),
                         (v₁ < 1024) ->
                          (v₁ ≥ 0) ->
                           ∀ (a'₁₁ : TcbPathHostPath),
                            (((TcbPathHostPath.depth a'₁₁) ≥ 0) ∧ (TcbPathHostPath.is_relative a'₁₁) ∧ (should_follow₀ -> (TcbPathHostPath.non_symlink a'₁₁)) ∧ (TcbPathHostPath.non_symlink_prefixes a'₁₁)) ->
                             ∀ (dflags₀ : Int),
                              ∀ (a'₁₃ : Int),
                               ∀ (a'₁₄ : Int),
                                ∀ (a'₁₅ : Int),
                                 ∀ (flags₀ : Int),
                                  ∀ (b₀ : Prop),
                                   ((b₀ = (flag_set flags₀ 131072)) ∧ (b₀ -> (flags₀ ≠ 0))) ->
                                    (b₀ ≠ should_follow₀) ->
                                     (¬(flag_set flags₀ types_O_NOFOLLOW)) ->
                                      (TcbPathHostPath.non_symlink a'₁₁)
end F
