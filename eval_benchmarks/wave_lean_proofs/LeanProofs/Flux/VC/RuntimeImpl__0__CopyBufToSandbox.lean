import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__CopyBufToSandbox := 
 ∀ (dummy₀ : TypesVmCtx),
  ∀ (n₀ : Int),
   ∀ (src₀ : Int),
    ∀ (n₁ : Int),
     (n₀ ≥ 0) ->
      (n₁ ≥ 0) ->
       (src₀ ≥ 0) ->
        (¬(src₀ < n₁)) ->
         ∀ (a'₃ : Prop),
          (a'₃ = ((((0 ≤ n₁) ∧ (n₀ ≤ (n₀ + n₁))) ∧ (0 ≤ n₀)) ∧ ((n₀ + n₁) < (0 + types_LINEAR_MEM_SIZE)))) ->
           a'₃ ->
            (((n₀ + n₁) < types_LINEAR_MEM_SIZE)) ∧
            ((n₁ ≤ src₀))
            
end F
