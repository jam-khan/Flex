import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FftLoopA := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (n₀ ≥ 0) ->
    (((n₀ - 1) ≥ 0)) ∧
    ((((k0 (n₀ - 1) ((n₀ - 1) / 4) n₀))) ∧
    (∀ (n2₀ : Int),
     ∀ (n4₀ : Int),
      ((k0 n2₀ n4₀ n₀)) ->
       (2 < n2₀) ->
        (((k1 1 n₀ n2₀ n4₀))) ∧
        (∀ (j₀ : Int),
         ((k1 j₀ n₀ n2₀ n4₀)) ->
          ((¬(j₀ ≤ n4₀)) ->
           ((k0 (n2₀ / 2) (n4₀ / 2) n₀))) ∧
          ((j₀ ≤ n4₀) ->
           (((k2 j₀ (2 * n2₀) n₀ n2₀ n4₀ j₀))) ∧
           (∀ (is₀ : Int),
            ∀ (id₀ : Int),
             ((k2 is₀ id₀ n₀ n2₀ n4₀ j₀)) ->
              ((¬(is₀ < (n₀ - 1))) ->
               ((k1 (j₀ + 1) n₀ n2₀ n4₀))) ∧
              ((is₀ < (n₀ - 1)) ->
               (((k3 is₀ (is₀ + n4₀) ((is₀ + n4₀) + n4₀) (((is₀ + n4₀) + n4₀) + n4₀) n₀ n2₀ n4₀ j₀ is₀ id₀))) ∧
               (∀ (i0₀ : Int),
                ∀ (i1₀ : Int),
                 ∀ (i2₀ : Int),
                  ∀ (i3₀ : Int),
                   ((k3 i0₀ i1₀ i2₀ i3₀ n₀ n2₀ n4₀ j₀ is₀ id₀)) ->
                    ((¬(i3₀ ≤ (n₀ - 1))) ->
                     ((((2 * id₀) - n2₀) ≥ 0)) ∧
                     (((k2 (((2 * id₀) - n2₀) + j₀) (4 * id₀) n₀ n2₀ n4₀ j₀)))
                     ) ∧
                    ((i3₀ ≤ (n₀ - 1)) ->
                     ((i0₀ < n₀)) ∧
                     ((i2₀ < n₀)) ∧
                     ((i0₀ < n₀)) ∧
                     ((i2₀ < n₀)) ∧
                     ((i0₀ < n₀)) ∧
                     ((i1₀ < n₀)) ∧
                     ((i3₀ < n₀)) ∧
                     ((i1₀ < n₀)) ∧
                     ((i3₀ < n₀)) ∧
                     ((i1₀ < n₀)) ∧
                     ((i0₀ < n₀)) ∧
                     ((i2₀ < n₀)) ∧
                     ((i0₀ < n₀)) ∧
                     ((i2₀ < n₀)) ∧
                     ((i0₀ < n₀)) ∧
                     ((i1₀ < n₀)) ∧
                     ((i3₀ < n₀)) ∧
                     ((i1₀ < n₀)) ∧
                     ((i3₀ < n₀)) ∧
                     ((i1₀ < n₀)) ∧
                     ((i2₀ < n₀)) ∧
                     ((i2₀ < n₀)) ∧
                     ((i3₀ < n₀)) ∧
                     ((i3₀ < n₀)) ∧
                     (((k3 (i0₀ + id₀) (i1₀ + id₀) (i2₀ + id₀) (i3₀ + id₀) n₀ n2₀ n4₀ j₀ is₀ id₀)))
                     )
                    )
               )
              )
           )
          )
        )
    )
    
end F
