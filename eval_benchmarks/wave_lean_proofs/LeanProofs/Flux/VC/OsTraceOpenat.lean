import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.User.Fun.FlagSet
import LeanProofs.Flux.Fun.TypesONOFOLLOW
import LeanProofs.Flux.Fun.UnixLinuxLikeLinuxGnuB64X8664ONOFOLLOW
open Classical
set_option linter.unusedVariables false


namespace F



def OsTraceOpenat := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (flags₀ : Int),
   ∀ (v₀ : TcbPathHostPath),
    (((TcbPathHostPath.depth v₀) ≥ 0) ∧ (TcbPathHostPath.is_relative v₀) ∧ ((¬(flag_set flags₀ types_O_NOFOLLOW)) -> (TcbPathHostPath.non_symlink v₀)) ∧ (TcbPathHostPath.non_symlink_prefixes v₀)) ->
     ((TypesVmCtx.homedir_host_fd cx₀) ≥ 0) ->
      (¬(flag_set flags₀ unix_linux_like_linux_gnu_b64_x86_64_O_NOFOLLOW)) ->
       (TcbPathHostPath.non_symlink v₀)
end F
