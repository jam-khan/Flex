import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoGetNth := 
 ∀ (l₀ : Int),
  ∀ (v₀ : Int),
   (v₀ < l₀) ->
    (l₀ ≥ 0) ->
     (v₀ ≥ 0) ->
      ((l₀ = 0) ->
       False) ∧
      (∀ (n₀ : Int),
       (l₀ = (n₀ + 1)) ->
        ∀ (a'₂ : Int),
         (n₀ ≥ 0) ->
          (v₀ ≠ 0) ->
           (((v₀ - 1) ≥ 0)) ∧
           (((v₀ - 1) < n₀))
           )
      
end F
