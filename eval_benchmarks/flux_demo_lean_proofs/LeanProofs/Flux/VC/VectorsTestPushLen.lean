import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsTestPushLen := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (((0 + 1) + 1) ≥ 0) ->
    ((((0 + 1) + 1) = 2) = True)
end F
