import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoTestRvec := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    ((((0 + 1) + 1) + 1) ≥ 0) ->
     (((((0 + 1) + 1) + 1) = 3) = True)
end F
