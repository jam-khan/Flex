import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.User.Fun.FlagSet
import LeanProofs.Flux.Fun.TypesATSYMLINKFOLLOW
import LeanProofs.Flux.Fun.UnixLinuxLikeATSYMLINKFOLLOW
open Classical
set_option linter.unusedVariables false


namespace F



def OsTraceLinkat := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (flags₀ : Int),
   ∀ (v₀ : TcbPathHostPath),
    ∀ (v₁ : TcbPathHostPath),
     (((TcbPathHostPath.depth v₀) ≥ 0) ∧ (TcbPathHostPath.is_relative v₀) ∧ ((flag_set flags₀ types_AT_SYMLINK_FOLLOW) -> (TcbPathHostPath.non_symlink v₀)) ∧ (TcbPathHostPath.non_symlink_prefixes v₀)) ->
      (((TcbPathHostPath.depth v₁) ≥ 0) ∧ (TcbPathHostPath.is_relative v₁) ∧ ((flag_set flags₀ types_AT_SYMLINK_FOLLOW) -> (TcbPathHostPath.non_symlink v₁)) ∧ (TcbPathHostPath.non_symlink_prefixes v₁)) ->
       ((TypesVmCtx.homedir_host_fd cx₀) ≥ 0) ->
        ((((TypesVmCtx.homedir_host_fd cx₀) = (TypesVmCtx.homedir_host_fd cx₀))) ∧
        (((TypesVmCtx.homedir_host_fd cx₀) = (TypesVmCtx.homedir_host_fd cx₀)))
        ) ∧
        ((flag_set flags₀ unix_linux_like_AT_SYMLINK_FOLLOW) ->
         (TcbPathHostPath.non_symlink v₀)) ∧
        ((flag_set flags₀ unix_linux_like_AT_SYMLINK_FOLLOW) ->
         (TcbPathHostPath.non_symlink v₁))
        
end F
