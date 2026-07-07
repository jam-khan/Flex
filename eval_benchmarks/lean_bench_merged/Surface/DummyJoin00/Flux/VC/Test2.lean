import Surface.DummyJoin00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (x₀ : Int),
  ((x₀ ≠ 0) ->
   ((x₀ ≠ 1) ->
    ((x₀ ≠ 2) ->
     ((k0 4 x₀))) ∧
    ((¬(x₀ ≠ 2)) ->
     ((k0 3 x₀)))
    ) ∧
   ((¬(x₀ ≠ 1)) ->
    ((k0 2 x₀)))
   ) ∧
  ((¬(x₀ ≠ 0)) ->
   ((k0 1 x₀))) ∧
  (∀ (res₀ : Int),
   ((k0 res₀ x₀)) ->
    ((2 ≤ (res₀ + 1))) ∧
    (((res₀ + 1) ≤ 5))
    )
  
end F
