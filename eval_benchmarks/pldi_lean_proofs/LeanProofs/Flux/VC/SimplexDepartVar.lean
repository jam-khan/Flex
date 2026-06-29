import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def SimplexDepartVar := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Prop) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   ∀ (j₀ : Int),
    ∀ (i0₀ : Int),
     ((0 < j₀) ∧ (j₀ < n₀)) ->
      ((0 < i0₀) ∧ (i0₀ < m₀)) ->
       (m₀ ≥ 0) ->
        (n₀ ≥ 0) ->
         (j₀ ≥ 0) ->
          (i0₀ ≥ 0) ->
           (((k0 i0₀ (i0₀ + 1) m₀ n₀ j₀ i0₀))) ∧
           (∀ (i₀ : Int),
            ∀ (i_₀ : Int),
             ((k0 i₀ i_₀ m₀ n₀ j₀ i0₀)) ->
              ((¬(i_₀ < m₀)) ->
               ((0 < i₀)) ∧
               ((i₀ < m₀))
               ) ∧
              ((i_₀ < m₀) ->
               ∀ (a'₂ : Prop),
                ((¬a'₂) ->
                 ((k1 i₀ m₀ n₀ j₀ i0₀ i₀ i_₀ a'₂))) ∧
                (a'₂ ->
                 (((n₀ - 1) ≥ 0)) ∧
                 (((n₀ - 1) < n₀)) ∧
                 (∀ (a'₃ : Prop),
                  ((¬a'₃) ->
                   ((k2 i₀ m₀ n₀ j₀ i0₀ i₀ i_₀ True a'₃))) ∧
                  (a'₃ ->
                   ((k2 i_₀ m₀ n₀ j₀ i0₀ i₀ i_₀ True True))) ∧
                  (∀ (i₁ : Int),
                   ((k2 i₁ m₀ n₀ j₀ i0₀ i₀ i_₀ True a'₃)) ->
                    ((k1 i₁ m₀ n₀ j₀ i0₀ i₀ i_₀ True)))
                  )
                 ) ∧
                (∀ (i₂ : Int),
                 ((k1 i₂ m₀ n₀ j₀ i0₀ i₀ i_₀ a'₂)) ->
                  ((k0 i₂ (i_₀ + 1) m₀ n₀ j₀ i0₀)))
                )
              )
           
end F
