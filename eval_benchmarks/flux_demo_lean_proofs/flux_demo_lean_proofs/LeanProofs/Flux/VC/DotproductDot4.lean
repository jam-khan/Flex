import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DotproductDot4 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (∀ (a'₀ : Int),
    ((k0 a'₀ n₀)) ->
     (a'₀ ≥ 0) ->
      (a'₀ < n₀)) ∧
   (∀ (item₀ : Int),
    ((0 ≤ item₀) ∧ (item₀ < n₀)) ->
     ((k0 item₀ n₀)))
   
end F
