import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__ReadU32Pair := 
 ∀ (a'₀ : TypesVmCtx),
  ∀ (start₀ : Int),
   (start₀ ≥ 0) ->
    ∀ (a'₂ : Prop),
     (a'₂ = (((start₀ ≤ (start₀ + 8)) ∧ (0 ≤ start₀)) ∧ ((start₀ + 8) < (0 + types_LINEAR_MEM_SIZE)))) ->
      a'₂ ->
       (((0 ≤ start₀)) ∧
       ((4 ≤ (4 + start₀))) ∧
       (((4 + start₀) < (0 + types_LINEAR_MEM_SIZE)))
       ) ∧
       (∀ (x1₀ : Int),
        (x1₀ ≥ 0) ->
         ((0 ≤ (start₀ + 4))) ∧
         ((4 ≤ (4 + (start₀ + 4)))) ∧
         (((4 + (start₀ + 4)) < (0 + types_LINEAR_MEM_SIZE)))
         )
       
end F
