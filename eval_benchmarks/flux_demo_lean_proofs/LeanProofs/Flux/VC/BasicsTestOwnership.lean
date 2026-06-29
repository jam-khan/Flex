import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BasicsTestOwnership := 
 ((((0 + 10) = 10) = True)) ∧
 (((((0 + 10) + 5) = 15) = True))
 
end F
