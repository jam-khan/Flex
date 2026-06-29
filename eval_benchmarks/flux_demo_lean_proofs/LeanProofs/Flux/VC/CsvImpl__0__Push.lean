import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def CsvImpl__0__Push := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (0 ≤ n₀) ->
    ∀ (a'₀ : Int),
     (∀ (a'₁ : Int),
      (a'₁ = n₀) ->
       ((k0 a'₁ n₀ a'₀))) ∧
     (((k0 n₀ n₀ a'₀))) ∧
     ((0 ≤ (a'₀ + 1)) ->
      ∀ (a'₂ : Int),
       ((k0 a'₂ n₀ a'₀)) ->
        (a'₂ = n₀))
     
end F
