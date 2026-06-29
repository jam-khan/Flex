import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FftFftTest := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Int) -> (a8 : Prop) -> Prop, 
 ∀ (np₀ : Int),
  (2 ≤ np₀) ->
   (np₀ ≥ 0) ->
    ((((np₀ / 2) - 1) ≥ 0)) ∧
    ((1 < (np₀ + 1))) ∧
    ((1 < (np₀ + 1))) ∧
    ((((np₀ / 2) + 1) < (np₀ + 1))) ∧
    ((((np₀ / 2) + 1) < (np₀ + 1))) ∧
    (((k0 1 np₀))) ∧
    (∀ (i₀ : Int),
     ((k0 i₀ np₀)) ->
      ((¬(i₀ ≤ ((np₀ / 2) - 1))) ->
       ((2 ≤ (np₀ + 1))) ∧
       (((k1 0 0 0 np₀ i₀))) ∧
       (∀ (_kr₀ : Int),
        ∀ (_ki₀ : Int),
         ∀ (i₁ : Int),
          ((k1 _kr₀ _ki₀ i₁ np₀ i₀)) ->
           (i₁ < np₀) ->
            (((i₁ + 1) < (np₀ + 1))) ∧
            (∀ (a'₄ : Prop),
             ((¬a'₄) ->
              ((k2 _kr₀ np₀ i₀ _kr₀ _ki₀ i₁ a'₄))) ∧
             (a'₄ ->
              ((k2 i₁ np₀ i₀ _kr₀ _ki₀ i₁ True))) ∧
             (∀ (_kr₁ : Int),
              ((k2 _kr₁ np₀ i₀ _kr₀ _ki₀ i₁ a'₄)) ->
               (((i₁ + 1) < (np₀ + 1))) ∧
               (∀ (a'₆ : Prop),
                ((¬a'₆) ->
                 ((k3 _ki₀ np₀ i₀ _kr₀ _ki₀ i₁ a'₄ _kr₁ a'₆))) ∧
                (a'₆ ->
                 ((k3 i₁ np₀ i₀ _kr₀ _ki₀ i₁ a'₄ _kr₁ True))) ∧
                (∀ (_ki₁ : Int),
                 ((k3 _ki₁ np₀ i₀ _kr₀ _ki₀ i₁ a'₄ _kr₁ a'₆)) ->
                  ((k1 _kr₁ _ki₁ (i₁ + 1) np₀ i₀)))
                )
               )
             )
            )
       ) ∧
      ((i₀ ≤ ((np₀ / 2) - 1)) ->
       (((np₀ - i₀) ≥ 0)) ∧
       (((i₀ + 1) < (np₀ + 1))) ∧
       ((((np₀ - i₀) + 1) < (np₀ + 1))) ∧
       (((i₀ + 1) < (np₀ + 1))) ∧
       ((((np₀ - i₀) + 1) < (np₀ + 1))) ∧
       (((k0 (i₀ + 1) np₀)))
       )
      )
    
end F
