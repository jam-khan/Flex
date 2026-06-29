import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BorrowsCheckVal := ∃ k0 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (a₀ : Int),
   ∀ (b₀ : Int),
    ((n₀ = a₀) ∨ (n₀ = b₀)) ->
     ((n₀ ≠ a₀) ->
      ((k0 (n₀ = b₀) n₀ a₀ b₀))) ∧
     ((¬(n₀ ≠ a₀)) ->
      ((k0 True n₀ a₀ b₀))) ∧
     (∀ (a'₀ : Prop),
      ((k0 a'₀ n₀ a₀ b₀)) ->
       (a'₀ = True))
     
end F
