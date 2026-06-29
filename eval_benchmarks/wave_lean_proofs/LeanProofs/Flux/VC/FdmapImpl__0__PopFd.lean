import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def FdmapImpl__0__PopFd := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (fd₀ : TypesFdMap),
  ((TypesFdMap.counter fd₀) ≥ 0) ->
   ((TypesFdMap.reserve_len fd₀) ≥ 0) ->
    ((¬((TypesFdMap.reserve_len fd₀) > 0)) ->
     ((TypesFdMap.counter fd₀) < 8) ->
      (((((TypesFdMap.counter fd₀) + 1) - 1) ≥ 0)) ∧
      (((k0 (((TypesFdMap.counter fd₀) + 1) - 1) (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀)))) ∧
      (∀ (a'₀ : Int),
       ((k0 a'₀ (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀))) ->
        (a'₀ < types_MAX_SBOX_FDS))
      ) ∧
    (((TypesFdMap.reserve_len fd₀) > 0) ->
     (((TypesFdMap.reserve_len fd₀) > 0)) ∧
     (∀ (v₀ : Int),
      (v₀ < types_MAX_SBOX_FDS) ->
       ((k1 v₀ (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀)))) ∧
     (∀ (a'₂ : Int),
      ((k1 a'₂ (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀))) ->
       (a'₂ ≥ 0) ->
        (((k2 a'₂ (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀) a'₂))) ∧
        (∀ (a'₃ : Int),
         ((k1 a'₃ (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀))) ->
          (a'₃ < types_MAX_SBOX_FDS)) ∧
        (∀ (a'₄ : Int),
         ((k2 a'₄ (TypesFdMap.reserve_len fd₀) (TypesFdMap.counter fd₀) a'₂)) ->
          (a'₄ < types_MAX_SBOX_FDS))
        )
     )
    
end F
