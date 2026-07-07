import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def SparseExample1 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> Prop, ∃ k5 : (a0 : Int) -> Prop, ∃ k6 : (a0 : Int) -> Prop, ∃ k7 : (a0 : Int) -> Prop, ∃ k8 : (a0 : Int) -> Prop, 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    (0 ≤ ((((0 + 1) + 1) + 1) + 1)) ->
     (((k0 0))) ∧
     ((∀ (a'₀ : Int),
      ((k0 a'₀)) ->
       ((k1 a'₀))) ∧
     (((k1 1))) ∧
     ((∀ (a'₁ : Int),
      ((k1 a'₁)) ->
       ((k2 a'₁))) ∧
     (((k2 2))) ∧
     ((∀ (a'₂ : Int),
      ((k2 a'₂)) ->
       ((k3 a'₂))) ∧
     (((k3 1))) ∧
     ((((k4 0))) ∧
     ((∀ (a'₃ : Int),
      ((k4 a'₃)) ->
       ((k5 a'₃))) ∧
     (((k5 1))) ∧
     ((∀ (a'₄ : Int),
      ((k5 a'₄)) ->
       ((k6 a'₄))) ∧
     (((k6 2))) ∧
     ((∀ (a'₅ : Int),
      ((k6 a'₅)) ->
       ((k7 a'₅))) ∧
     (((k7 3))) ∧
     ((∀ (a'₆ : Int),
      ((k7 a'₆)) ->
       ((k8 a'₆))) ∧
     (((k8 4))) ∧
     ((0 ≤ (((((0 + 1) + 1) + 1) + 1) + 1)) ->
      (∀ (a'₇ : Int),
       ((k3 a'₇)) ->
        (a'₇ < 4)) ∧
      (∀ (a'₈ : Int),
       ((k8 a'₈)) ->
        (a'₈ ≤ ((((0 + 1) + 1) + 1) + 1))) ∧
      (((((((0 + 1) + 1) + 1) + 1) + 1) = (4 + 1)))
      )
     )
     )
     )
     )
     )
     )
     )
     )
     
end F
