import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibSpecFib
open Classical
set_option linter.unusedVariables false


namespace F



def FibFibFast := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((¬(n₀ ≤ 1)) ->
    (((k0 1 2 2 n₀))) ∧
    (∀ (prev₀ : Int),
     ∀ (curr₀ : Int),
      ∀ (i₀ : Int),
       ((k0 prev₀ curr₀ i₀ n₀)) ->
        ((¬(i₀ < n₀)) ->
         (curr₀ = (fib_spec_fib n₀))) ∧
        ((i₀ < n₀) ->
         ((k0 curr₀ (prev₀ + curr₀) (i₀ + 1) n₀)))
        )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_spec_fib n₀)))
   
end F
