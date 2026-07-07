import Surface.ReadLoop.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RefJoin := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  (((k0 0 b₀))) ∧
  (∀ (r₀ : Int),
   ((k0 r₀ b₀)) ->
    ((¬b₀) ->
     (((r₀ + 1) > 0) = True)) ∧
    (b₀ ->
     ((k0 1 True)))
    )
  
end F
