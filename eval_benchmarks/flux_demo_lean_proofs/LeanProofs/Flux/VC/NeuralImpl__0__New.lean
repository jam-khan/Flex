import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def NeuralImpl__0__New := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (i₀ : Int),
  ∀ (o₀ : Int),
   (i₀ ≥ 0) ->
    (o₀ ≥ 0) ->
     (((k0 i₀ o₀))) ∧
     (∀ (a'₀ : Int),
      ((k1 a'₀ i₀ o₀)) ->
       (a'₀ ≥ 0) ->
        (∀ (a'₁ : Int),
         ((k2 a'₁ i₀ o₀ a'₀)) ->
          (a'₁ ≥ 0) ->
           ((k0 i₀ o₀))) ∧
        (∀ (v₀ : Int),
         ((0 ≤ v₀) ∧ (v₀ < i₀)) ->
          ((k2 v₀ i₀ o₀ a'₀))) ∧
        (((k0 i₀ o₀)) ->
         ((k3 i₀ o₀ a'₀))) ∧
        (((k3 i₀ o₀ a'₀)) ->
         ((k0 i₀ o₀))) ∧
        ((0 ≤ i₀) ->
         ((k4 i₀ a'₀ i₀ o₀)))
        ) ∧
     (∀ (v₁ : Int),
      ((0 ≤ v₁) ∧ (v₁ < o₀)) ->
       (((k1 v₁ i₀ o₀))) ∧
       (∀ (a'₄ : Int),
        ((k4 a'₄ v₁ i₀ o₀)) ->
         ((k5 a'₄ i₀ o₀)))
       ) ∧
     (((k0 i₀ o₀)) ->
      ((k6 i₀ o₀))) ∧
     (((k6 i₀ o₀)) ->
      ((k0 i₀ o₀))) ∧
     ((0 ≤ o₀) ->
      ((k0 i₀ o₀)) ->
       (((k7 i₀ o₀))) ∧
       (∀ (a'₅ : Int),
        ((k8 a'₅ i₀ o₀)) ->
         (a'₅ ≥ 0) ->
          ((k7 i₀ o₀))) ∧
       (∀ (v₂ : Int),
        ((0 ≤ v₂) ∧ (v₂ < o₀)) ->
         ((k8 v₂ i₀ o₀))) ∧
       (((k7 i₀ o₀)) ->
        ((k9 i₀ o₀))) ∧
       (((k9 i₀ o₀)) ->
        ((k7 i₀ o₀))) ∧
       (((k7 i₀ o₀)) ->
        ∀ (a'₇ : Int),
         ((k5 a'₇ i₀ o₀)) ->
          (a'₇ = i₀))
       )
     
end F
