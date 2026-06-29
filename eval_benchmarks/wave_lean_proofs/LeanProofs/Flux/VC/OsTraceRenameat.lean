import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesVmCtx
open Classical
set_option linter.unusedVariables false


namespace F



def OsTraceRenameat := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (v₀ : TcbPathHostPath),
   ∀ (v₁ : TcbPathHostPath),
    (((TcbPathHostPath.depth v₀) ≥ 0) ∧ (TcbPathHostPath.is_relative v₀) ∧ (False -> (TcbPathHostPath.non_symlink v₀)) ∧ (TcbPathHostPath.non_symlink_prefixes v₀)) ->
     (((TcbPathHostPath.depth v₁) ≥ 0) ∧ (TcbPathHostPath.is_relative v₁) ∧ (False -> (TcbPathHostPath.non_symlink v₁)) ∧ (TcbPathHostPath.non_symlink_prefixes v₁)) ->
      ((TypesVmCtx.homedir_host_fd cx₀) ≥ 0) ->
       (((TypesVmCtx.homedir_host_fd cx₀) = (TypesVmCtx.homedir_host_fd cx₀))) ∧
       (((TypesVmCtx.homedir_host_fd cx₀) = (TypesVmCtx.homedir_host_fd cx₀)))
       
end F
