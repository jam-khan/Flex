import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BorrowsAliasing := 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   (((20 + 1) = 21) = True)) ∧
  (b₀ ->
   (((10 + 1) = 11) = True))
  
end F
