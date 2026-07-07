import Surface.Date.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsFebDay := 
 ∀ (d₀ : Int),
  ∀ (y₀ : Int),
   (d₀ ≥ 0) ->
    (y₀ ≥ 0) ->
     ((¬(d₀ ≤ 29)) ->
      (False = ((d₀ ≤ 29) ∧ ((d₀ = 29) -> (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))))))) ∧
     ((d₀ ≤ 29) ->
      ((¬(d₀ ≠ 29)) ->
       ((((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))) = ((d₀ = 29) -> (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0)))))) ∧
      ((d₀ ≠ 29) ->
       (True = ((d₀ = 29) -> (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))))))
      )
     
end F
