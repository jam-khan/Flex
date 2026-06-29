import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def FdmapImpl__0__Create := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (dummy₀ : TypesFdMap),
  ∀ (k₀ : Int),
   ∀ (self₀ : TypesFdMap),
    (∀ (v₀ : Int),
     (v₀ < types_MAX_SBOX_FDS) ->
      ((k0 v₀ (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) k₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
    (∀ (a'₃ : Int),
     ((k0 a'₃ (TypesFdMap.reserve_len dummy₀) (TypesFdMap.counter dummy₀) k₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
      (a'₃ ≥ 0) ->
       ((TypesFdMap.counter self₀) ≥ 0) ->
        ((0 ≤ a'₃)) ∧
        ((a'₃ < types_MAX_SBOX_FDS))
        )
    
end F
