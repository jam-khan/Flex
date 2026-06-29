import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__WriteU16 := 
 ∀ (cx₀ : TypesVmCtx),
  ∀ (cnt₀ : Int),
   ∀ (v₀ : Int),
    ((0 ≤ cnt₀) ∧ (2 ≤ (2 + cnt₀)) ∧ ((2 + cnt₀) < (0 + types_LINEAR_MEM_SIZE))) ->
     (cnt₀ ≥ 0) ->
      (v₀ ≥ 0) ->
       ∀ (a'₂ : Int),
        (a'₂ ≥ 0) ->
         (((1 ≤ (1 + cnt₀))) ∧
         (((1 + cnt₀) < (0 + types_LINEAR_MEM_SIZE)))
         ) ∧
         (∀ (a'₃ : Int),
          (a'₃ ≥ 0) ->
           ((0 ≤ (cnt₀ + 1))) ∧
           ((1 ≤ (1 + (cnt₀ + 1)))) ∧
           (((1 + (cnt₀ + 1)) < (0 + types_LINEAR_MEM_SIZE)))
           )
         
end F
