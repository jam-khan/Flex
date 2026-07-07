import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BorrowsTestIncMut := 
 (((1 ≤ (1 + 1)) = True)) ∧
 (((1 ≤ ((1 + 1) + 1)) = True)) ∧
 (((2 ≤ ((1 + 1) + 1)) = True))
 
end F
