import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__TranslatePath := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (should_follow₀ : Prop),
   ∀ (n₀ : Int),
    ∀ (path_len₀ : Int),
     ∀ (dirfd₀ : Int),
      (n₀ ≥ 0) ->
       (path_len₀ ≥ 0) ->
        ∀ (a'₃ : Prop),
         (a'₃ = ((((0 ≤ path_len₀) ∧ (n₀ ≤ (n₀ + path_len₀))) ∧ (0 ≤ n₀)) ∧ ((n₀ + path_len₀) < (0 + types_LINEAR_MEM_SIZE)))) ->
          a'₃ ->
           ((0 ≤ path_len₀)) ∧
           (((n₀ + path_len₀) < types_LINEAR_MEM_SIZE))
           
end F
