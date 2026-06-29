import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def FdmapImpl__0__FdToNative := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (v_fd₀ : Int),
  ∀ (self₀ : TypesFdMap),
   (v_fd₀ ≥ 0) ->
    (¬(v_fd₀ ≥ 8)) ->
     ((TypesFdMap.counter self₀) ≥ 0) ->
      (((0 ≤ v_fd₀)) ∧
      ((v_fd₀ < types_MAX_SBOX_FDS))
      ) ∧
      (((k0 v_fd₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
      (∀ (a'₁ : Int),
       ((k1 a'₁ v_fd₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
      (((k0 v_fd₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
       ∀ (a'₂ : Int),
        ((k1 a'₂ v_fd₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
         (v_fd₀ < types_MAX_SBOX_FDS))
      
end F
