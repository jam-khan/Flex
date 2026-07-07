import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsDot := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (m₀ : Int),
   (n₀ = m₀) ->
    (0 ≤ n₀) ->
     (0 ≤ m₀) ->
      (n₀ ≥ 0) ->
       (((k0 0 n₀ m₀))) ∧
       (∀ (i₀ : Int),
        ((k0 i₀ n₀ m₀)) ->
         (i₀ < n₀) ->
          ((i₀ < m₀)) ∧
          (((k0 (i₀ + 1) n₀ m₀)))
          )
       
end F
