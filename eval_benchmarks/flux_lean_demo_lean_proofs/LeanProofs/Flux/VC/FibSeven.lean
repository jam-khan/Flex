import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibSpecSeven
open Classical
set_option linter.unusedVariables false


namespace F



def FibSeven := 
 (((3 + 2) + 2) = (fib_spec_seven))
end F
