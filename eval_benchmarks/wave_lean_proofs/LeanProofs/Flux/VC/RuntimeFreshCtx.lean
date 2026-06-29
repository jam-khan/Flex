import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeFreshCtx := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (self₀ : TypesFdMap),
  ∀ (a'₁ : Int),
   ∀ (a'₂ : Int),
    (a'₂ ≥ 0) ->
     ((a'₁ ≥ 0) -> (a'₂ = a'₁)) ->
      (∀ (self₁ : TypesFdMap),
       ((k0 (TypesFdMap.reserve_len self₁) (TypesFdMap.counter self₁) (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀) a'₁ a'₂))) ∧
      (∀ (fdmap₀ : TypesFdMap),
       ((k0 (TypesFdMap.reserve_len fdmap₀) (TypesFdMap.counter fdmap₀) (TypesFdMap.reserve_len self₀) (TypesFdMap.counter self₀) a'₁ a'₂)) ->
        ∀ (netlist₀ : Int),
         ((4294965096 = types_LINEAR_MEM_SIZE)) ∧
         ((4294965096 = types_LINEAR_MEM_SIZE)) ∧
         ((0 < types_TWO_POWER_20)) ∧
         ((0 < types_TWO_POWER_20))
         )
      
end F
