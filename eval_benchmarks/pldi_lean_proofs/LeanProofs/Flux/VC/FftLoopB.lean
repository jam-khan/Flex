import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FftLoopB := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (n₀ ≥ 0) ->
    (((n₀ - 1) ≥ 0)) ∧
    (((k0 1 4 n₀))) ∧
    (∀ (is₀ : Int),
     ∀ (id₀ : Int),
      ((k0 is₀ id₀ n₀)) ->
       (is₀ < (n₀ - 1)) ->
        (((k1 is₀ (is₀ + 1) n₀ is₀ id₀))) ∧
        (∀ (i0₀ : Int),
         ∀ (i1₀ : Int),
          ((k1 i0₀ i1₀ n₀ is₀ id₀)) ->
           ((¬(i1₀ ≤ (n₀ - 1))) ->
            ((((2 * id₀) - 1) ≥ 0)) ∧
            (((k0 ((2 * id₀) - 1) (4 * id₀) n₀)))
            ) ∧
           ((i1₀ ≤ (n₀ - 1)) ->
            ((i0₀ < n₀)) ∧
            ((i1₀ < n₀)) ∧
            ((i0₀ < n₀)) ∧
            ((i1₀ < n₀)) ∧
            ((i1₀ < n₀)) ∧
            ((i0₀ < n₀)) ∧
            ((i1₀ < n₀)) ∧
            ((i0₀ < n₀)) ∧
            ((i1₀ < n₀)) ∧
            ((i1₀ < n₀)) ∧
            (((k1 (i0₀ + id₀) (i1₀ + id₀) n₀ is₀ id₀)))
            )
           )
        )
    
end F
