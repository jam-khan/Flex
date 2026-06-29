import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def OsTraceReadlinkat := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (ptr₀ : Int),
   ∀ (v₀ : TcbPathHostPath),
    ∀ (cnt₀ : Int),
     (((TcbPathHostPath.depth v₀) ≥ 0) ∧ (TcbPathHostPath.is_relative v₀) ∧ (False -> (TcbPathHostPath.non_symlink v₀)) ∧ (TcbPathHostPath.non_symlink_prefixes v₀)) ->
      ((0 ≤ cnt₀) ∧ (ptr₀ ≤ (ptr₀ + cnt₀)) ∧ (0 ≤ ptr₀) ∧ ((ptr₀ + cnt₀) < (0 + types_LINEAR_MEM_SIZE)) ∧ (cnt₀ < types_LINEAR_MEM_SIZE)) ->
       (ptr₀ ≥ 0) ->
        (cnt₀ ≥ 0) ->
         ((((TypesVmCtx.base cx₀) + ptr₀) ≤ (((TypesVmCtx.base cx₀) + ptr₀) + cnt₀)) ∧ ((TypesVmCtx.base cx₀) ≤ ((TypesVmCtx.base cx₀) + ptr₀)) ∧ ((((TypesVmCtx.base cx₀) + ptr₀) + cnt₀) < ((TypesVmCtx.base cx₀) + types_LINEAR_MEM_SIZE))) ->
          ((TypesVmCtx.homedir_host_fd cx₀) ≥ 0) ->
           (cnt₀ ≥ cnt₀)
end F
