import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibSpecFib
open Classical
set_option linter.unusedVariables false


namespace F



def MemoFibMemo := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((¬(n₀ ≤ 1)) ->
    ∀ (a'₀ : Prop),
     (a'₀ = False) ->
      (((n₀ - 1) ≥ 0)) ∧
      (((fib_spec_fib (n₀ - 1)) ≥ 0) ->
       (((n₀ - 2) ≥ 0)) ∧
       (((fib_spec_fib (n₀ - 2)) ≥ 0) ->
        ((((fib_spec_fib (n₀ - 1)) + (fib_spec_fib (n₀ - 2))) = (fib_spec_fib n₀))) ∧
        ((((fib_spec_fib (n₀ - 1)) + (fib_spec_fib (n₀ - 2))) = (fib_spec_fib n₀)))
        )
       )
      ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_spec_fib n₀)))
   
end F
