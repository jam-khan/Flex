import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsTestRvec0 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, 
 (((k0 10))) ∧
 ((0 ≤ (0 + 1)) ->
  (∀ (a'₀ : Int),
   ((k0 a'₀)) ->
    ((k1 a'₀))) ∧
  (((k1 20))) ∧
  ((0 ≤ ((0 + 1) + 1)) ->
   (∀ (a'₁ : Int),
    ((k1 a'₁)) ->
     ((k2 a'₁))) ∧
   (((k2 30))) ∧
   ((0 ≤ (((0 + 1) + 1) + 1)) ->
    ((0 < (((0 + 1) + 1) + 1))) ∧
    (∀ (a'₂ : Int),
     ((k2 a'₂)) ->
      ((k3 a'₂))) ∧
    (∀ (a'₃ : Int),
     ((k3 a'₃)) ->
      (a'₃ ≥ 0) ->
       (10 ≤ a'₃))
    )
   )
  )
 
end F
