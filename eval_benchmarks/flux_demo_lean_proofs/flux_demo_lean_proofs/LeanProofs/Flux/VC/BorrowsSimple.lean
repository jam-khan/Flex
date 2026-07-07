import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BorrowsSimple := 
 ((((0 + 10) = 10) = True)) ∧
 (((((0 + 10) + 10) = 20) = True))
 
end F
