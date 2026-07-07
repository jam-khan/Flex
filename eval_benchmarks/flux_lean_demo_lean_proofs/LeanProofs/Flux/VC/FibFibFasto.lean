import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibSpecFib
import LeanProofs.Flux.Fun.NumImpl11MAX
open Classical
set_option linter.unusedVariables false


namespace F



def FibFibFasto := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ((fib_spec_fib n₀) < num_impl_11_MAX) ->
   (n₀ ≥ 0) ->
    (n₀ ≤ 18446744073709551615) ->
     ((¬(n₀ ≤ 1)) ->
      (((k0 1 2 2 n₀))) ∧
      (∀ (prev₀ : Int),
       ∀ (curr₀ : Int),
        ∀ (i₀ : Int),
         ((k0 prev₀ curr₀ i₀ n₀)) ->
          ((¬(i₀ < n₀)) ->
           (curr₀ = (fib_spec_fib n₀))) ∧
          ((i₀ < n₀) ->
           ((((prev₀ + curr₀) ≥ 0)) ∧
           (((prev₀ + curr₀) ≤ 18446744073709551615))
           ) ∧
           ((((i₀ + 1) ≥ 0)) ∧
           (((i₀ + 1) ≤ 18446744073709551615))
           ) ∧
           (((k0 curr₀ (prev₀ + curr₀) (i₀ + 1) n₀)))
           )
          )
      ) ∧
     ((n₀ ≤ 1) ->
      (1 = (fib_spec_fib n₀)))
     
end F
