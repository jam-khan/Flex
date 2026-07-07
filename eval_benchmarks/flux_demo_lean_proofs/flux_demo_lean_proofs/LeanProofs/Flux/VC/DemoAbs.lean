import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoAbs := 
 ∀ (n₀ : Int),
  ((¬(n₀ > 0)) ->
   ((0 ≤ (0 - n₀))) ∧
   ((n₀ ≤ (0 - n₀)))
   ) ∧
  ((n₀ > 0) ->
   ((0 ≤ n₀)) ∧
   ((n₀ ≤ n₀))
   )
  
end F
