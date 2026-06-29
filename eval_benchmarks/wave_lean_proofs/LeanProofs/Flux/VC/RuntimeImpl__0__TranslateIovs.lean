import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesNativeIoVec
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__TranslateIovs := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (iovs₀ : Int),
   (iovs₀ ≥ 0) ->
    (((k0 0 0 (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀))) ∧
    (∀ (idx₀ : Int),
     ∀ (native_iovs₀ : Int),
      ((k0 idx₀ native_iovs₀ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀)) ->
       ((¬(idx₀ < iovs₀)) ->
        ∀ (a'₃ : TypesNativeIoVec),
         ((k1 (TypesNativeIoVec.iov_base a'₃) (TypesNativeIoVec.iov_len a'₃) idx₀ native_iovs₀ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀)) ->
          (((TypesNativeIoVec.iov_base a'₃) + (TypesNativeIoVec.iov_len a'₃)) ≤ ((TypesVmCtx.base cx₀) + types_LINEAR_MEM_SIZE))) ∧
       ((idx₀ < iovs₀) ->
        ((0 ≤ idx₀)) ∧
        (∀ (a'₄ : Int),
         ((k2 a'₄ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀ idx₀ native_iovs₀))) ∧
        (∀ (a'₅ : Int),
         ((k2 a'₅ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀ idx₀ native_iovs₀)) ->
          ∀ (native_iov₀ : TypesNativeIoVec),
           (((TypesNativeIoVec.iov_base native_iov₀) + (TypesNativeIoVec.iov_len native_iov₀)) ≤ ((TypesVmCtx.base cx₀) + types_LINEAR_MEM_SIZE)) ->
            (∀ (a'₇ : TypesNativeIoVec),
             ((k1 (TypesNativeIoVec.iov_base a'₇) (TypesNativeIoVec.iov_len a'₇) idx₀ native_iovs₀ (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀)) ->
              ((k3 (TypesNativeIoVec.iov_base a'₇) (TypesNativeIoVec.iov_len a'₇) (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀ idx₀ native_iovs₀ a'₅ (TypesNativeIoVec.iov_base native_iov₀) (TypesNativeIoVec.iov_len native_iov₀)))) ∧
            (((k3 (TypesNativeIoVec.iov_base native_iov₀) (TypesNativeIoVec.iov_len native_iov₀) (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀ idx₀ native_iovs₀ a'₅ (TypesNativeIoVec.iov_base native_iov₀) (TypesNativeIoVec.iov_len native_iov₀)))) ∧
            (((k0 (idx₀ + 1) (native_iovs₀ + 1) (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀))) ∧
            (∀ (a'₈ : TypesNativeIoVec),
             ((k3 (TypesNativeIoVec.iov_base a'₈) (TypesNativeIoVec.iov_len a'₈) (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀ idx₀ native_iovs₀ a'₅ (TypesNativeIoVec.iov_base native_iov₀) (TypesNativeIoVec.iov_len native_iov₀))) ->
              ((k1 (TypesNativeIoVec.iov_base a'₈) (TypesNativeIoVec.iov_len a'₈) (idx₀ + 1) (native_iovs₀ + 1) (TypesVmCtx.arg_buf cx₀) (TypesVmCtx.env_buf cx₀) (TypesVmCtx.base cx₀) (TypesVmCtx.homedir_host_fd cx₀) (TypesVmCtx.net cx₀) iovs₀)))
            )
        )
       )
    
end F
