import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TcbPathHostPath
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def WrappersWasiPathReadlink := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (v_fd₀ : Int),
   ∀ (pathname₀ : Int),
    ∀ (path_len₀ : Int),
     ∀ (ptr₀ : Int),
      ∀ (len₀ : Int),
       (v_fd₀ ≥ 0) ->
        (pathname₀ ≥ 0) ->
         (path_len₀ ≥ 0) ->
          (ptr₀ ≥ 0) ->
           (len₀ ≥ 0) ->
            (¬(v_fd₀ ≠ 3)) ->
             (¬(v_fd₀ ≠ 3)) ->
              ((TypesVmCtx.base cx₀) ≥ 0) ->
               (types_LINEAR_MEM_SIZE ≥ 0) ->
                ((TypesVmCtx.arg_buf cx₀) < types_TWO_POWER_20) ->
                 ((TypesVmCtx.env_buf cx₀) < types_TWO_POWER_20) ->
                  ∀ (a'₅ : TcbPathHostPath),
                   (((TcbPathHostPath.depth a'₅) ≥ 0) ∧ (TcbPathHostPath.is_relative a'₅) ∧ (False -> (TcbPathHostPath.non_symlink a'₅)) ∧ (TcbPathHostPath.non_symlink_prefixes a'₅)) ->
                    ∀ (a'₆ : Prop),
                     (a'₆ = ((((0 ≤ len₀) ∧ (ptr₀ ≤ (ptr₀ + len₀))) ∧ (0 ≤ ptr₀)) ∧ ((ptr₀ + len₀) < (0 + types_LINEAR_MEM_SIZE)))) ->
                      a'₆ ->
                       ((0 ≤ len₀)) ∧
                       ((ptr₀ ≤ (ptr₀ + len₀))) ∧
                       ((0 ≤ ptr₀)) ∧
                       (((ptr₀ + len₀) < (0 + types_LINEAR_MEM_SIZE))) ∧
                       ((len₀ < types_LINEAR_MEM_SIZE))
                       
end F
