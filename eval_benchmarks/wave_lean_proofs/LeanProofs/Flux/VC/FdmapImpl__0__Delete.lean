import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesMAXSBOXFDS
open Classical
set_option linter.unusedVariables false


namespace F



def FdmapImpl__0__Delete := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (v₀ : Int),
  ∀ (self₀ : TypesFdMap),
   (v₀ < types_MAX_SBOX_FDS) ->
    (v₀ ≥ 0) ->
     ((TypesFdMap.counter self₀) ≥ 0) ->
      ((0 ≤ v₀)) ∧
      (((k0 v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
      (∀ (a'₂ : Int),
       ((k1 a'₂ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
      (((k2 v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
      (((k0 v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
       (∀ (a'₃ : Int),
        ((k1 a'₃ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
         (∀ (v₁ : Int),
          (v₁ < types_MAX_SBOX_FDS) ->
           ((k3 v₁ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀) a'₃))) ∧
         (((k3 v₀ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀) a'₃))) ∧
         (((k4 ((TypesFdMap.reserve_len self₀) + 1) v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
         (∀ (a'₅ : Int),
          ((k3 a'₅ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀) a'₃)) ->
           ((k5 a'₅ ((TypesFdMap.reserve_len self₀) + 1) v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))))
         ) ∧
       (((k2 v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
        (((k4 (TypesFdMap.reserve_len self₀) v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀)))) ∧
        (∀ (v₂ : Int),
         (v₂ < types_MAX_SBOX_FDS) ->
          ((k5 v₂ (TypesFdMap.reserve_len self₀) v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))))
        ) ∧
       (∀ (a'₇ : Int),
        ((k4 a'₇ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
         ((0 ≤ v₀)) ∧
         (∀ (a'₈ : Int),
          ((k5 a'₈ a'₇ v₀ (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀))) ->
           (a'₈ < types_MAX_SBOX_FDS))
         )
       )
      
end F
