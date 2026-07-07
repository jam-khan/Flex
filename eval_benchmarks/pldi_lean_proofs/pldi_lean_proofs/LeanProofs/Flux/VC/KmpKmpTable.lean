import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmpKmpTable := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (len₀ : Int),
  (0 < len₀) ->
   (len₀ ≥ 0) ->
    (((k0 0 len₀))) ∧
    (((k1 1 0 len₀))) ∧
    (∀ (a'₀ : Int),
     ((k0 a'₀ len₀)) ->
      ((k2 a'₀ 1 0 len₀))) ∧
    (∀ (i₀ : Int),
     ∀ (j₀ : Int),
      ((k1 i₀ j₀ len₀)) ->
       ((¬(i₀ < len₀)) ->
        ∀ (a'₃ : Int),
         ((k2 a'₃ i₀ j₀ len₀)) ->
          (a'₃ < len₀)) ∧
       ((i₀ < len₀) ->
        ∀ (a'₄ : Int),
         (a'₄ ≥ 0) ->
          ((j₀ < len₀)) ∧
          (∀ (a'₅ : Int),
           (a'₅ ≥ 0) ->
            ((a'₄ ≠ a'₅) ->
             ((j₀ ≠ 0) ->
              (((j₀ - 1) ≥ 0)) ∧
              (((j₀ - 1) < len₀)) ∧
              (∀ (a'₆ : Int),
               ((k2 a'₆ i₀ j₀ len₀)) ->
                ((k3 a'₆ len₀ i₀ j₀ a'₄ a'₅))) ∧
              (∀ (a'₇ : Int),
               ((k3 a'₇ len₀ i₀ j₀ a'₄ a'₅)) ->
                (a'₇ ≥ 0) ->
                 (((k4 i₀ a'₇ len₀ i₀ j₀ a'₄ a'₅))) ∧
                 (∀ (a'₈ : Int),
                  ((k2 a'₈ i₀ j₀ len₀)) ->
                   ((k5 a'₈ i₀ a'₇ len₀ i₀ j₀ a'₄ a'₅)))
                 )
              ) ∧
             ((¬(j₀ ≠ 0)) ->
              (∀ (a'₉ : Int),
               ((k2 a'₉ i₀ j₀ len₀)) ->
                ((k6 a'₉ len₀ i₀ j₀ a'₄ a'₅))) ∧
              (((k6 0 len₀ i₀ j₀ a'₄ a'₅))) ∧
              (((k4 (i₀ + 1) j₀ len₀ i₀ j₀ a'₄ a'₅))) ∧
              (∀ (a'₁₀ : Int),
               ((k6 a'₁₀ len₀ i₀ j₀ a'₄ a'₅)) ->
                ((k5 a'₁₀ (i₀ + 1) j₀ len₀ i₀ j₀ a'₄ a'₅)))
              )
             ) ∧
            ((¬(a'₄ ≠ a'₅)) ->
             (∀ (a'₁₁ : Int),
              ((k2 a'₁₁ i₀ j₀ len₀)) ->
               ((k7 a'₁₁ len₀ i₀ j₀ a'₄ a'₅))) ∧
             (((k7 (j₀ + 1) len₀ i₀ j₀ a'₄ a'₅))) ∧
             (((k4 (i₀ + 1) (j₀ + 1) len₀ i₀ j₀ a'₄ a'₅))) ∧
             (∀ (a'₁₂ : Int),
              ((k7 a'₁₂ len₀ i₀ j₀ a'₄ a'₅)) ->
               ((k5 a'₁₂ (i₀ + 1) (j₀ + 1) len₀ i₀ j₀ a'₄ a'₅)))
             ) ∧
            (∀ (i₁ : Int),
             ∀ (j₁ : Int),
              ((k4 i₁ j₁ len₀ i₀ j₀ a'₄ a'₅)) ->
               (((k1 i₁ j₁ len₀))) ∧
               (∀ (a'₁₅ : Int),
                ((k5 a'₁₅ i₁ j₁ len₀ i₀ j₀ a'₄ a'₅)) ->
                 ((k2 a'₁₅ i₁ j₁ len₀)))
               )
            )
          )
       )
    
end F
