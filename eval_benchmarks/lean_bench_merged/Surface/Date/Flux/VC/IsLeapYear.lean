import Surface.Date.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsLeapYear := 
 ∀ (y₀ : Int),
  (y₀ ≥ 0) ->
   (((y₀ % 400) ≠ 0) ->
    (((y₀ % 4) ≠ 0) ->
     (False = (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))))) ∧
    ((¬((y₀ % 4) ≠ 0)) ->
     (((y₀ % 100) ≠ 0) = (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0)))))
    ) ∧
   ((¬((y₀ % 400) ≠ 0)) ->
    (True = (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0)))))
   
end F
