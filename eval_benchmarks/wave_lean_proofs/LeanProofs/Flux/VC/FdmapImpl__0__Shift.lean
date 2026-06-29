import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def FdmapImpl__0__Shift := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (dummy₀ : TypesFdMap),
  ∀ (v₀ : Int),
   ∀ (v₁ : Int),
    (v₀ < types_MAX_SBOX_FDS) ->
     (v₁ < types_MAX_SBOX_FDS) ->
      (v₀ ≥ 0) ->
       (v₁ ≥ 0) ->
        ((TypesFdMap.counter dummy₀) ≥ 0) ->
         ((0 ≤ v₀)) ∧
         (((k0 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁))) ∧
         (∀ (a'₂ : Int),
          ((k1 a'₂ (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁))) ∧
         (((k2 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁))) ∧
         (((k0 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁)) ->
          (∀ (a'₃ : Int),
           ((k1 a'₃ (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁)) ->
            ((0 ≤ v₁)) ∧
            (((k3 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁)))
            ) ∧
          (((k2 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁)) ->
           ((k3 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁))) ∧
          (((k3 (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) v₀ v₁)) ->
           (0 ≤ v₀))
          )
         
end F
