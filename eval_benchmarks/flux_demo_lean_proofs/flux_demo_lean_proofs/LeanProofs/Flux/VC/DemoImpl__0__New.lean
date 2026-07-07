import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def DemoImpl__0__New := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> Prop, 
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
        (∀ (a'₂ : Int),
         ((k2 a'₂ i₀ o₀ a'₀))) ∧
        (((k0 i₀ o₀)) ->
         ((k3 i₀ o₀ a'₀))) ∧
        (((k3 i₀ o₀ a'₀)) ->
         ((k0 i₀ o₀))) ∧
        ((0 ≤ i₀) ->
         ((k4 i₀ a'₀ i₀ o₀)))
        ) ∧
     (∀ (a'₃ : Int),
      (((k1 a'₃ i₀ o₀))) ∧
      (∀ (a'₄ : Int),
       ((k4 a'₄ a'₃ i₀ o₀)) ->
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
       (∀ (a'₆ : Int),
        ((k8 a'₆ i₀ o₀))) ∧
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
