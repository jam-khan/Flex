import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BasicsAbs := 
 ∀ (n₀ : Int),
  ((¬(n₀ < 0)) ->
   ((0 ≤ n₀)) ∧
   ((n₀ ≤ n₀))
   ) ∧
  ((n₀ < 0) ->
   ((0 ≤ (0 - n₀))) ∧
   ((n₀ ≤ (0 - n₀)))
   )
  
end F
