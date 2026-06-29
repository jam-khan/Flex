import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.DemoLayer
open Classical
set_option linter.unusedVariables false


namespace F



def DemoImpl__0__Forward := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (l₀ : DemoLayer),
  (0 ≤ (DemoLayer.i l₀)) ->
   ((DemoLayer.i l₀) ≥ 0) ->
    ((DemoLayer.o l₀) ≥ 0) ->
     (0 ≤ (DemoLayer.o l₀)) ->
      (∀ (a'₀ : Int),
       ((k0 a'₀ (DemoLayer.i l₀) (DemoLayer.o l₀))) ->
        (a'₀ ≥ 0) ->
         ((a'₀ < (DemoLayer.o l₀))) ∧
         (∀ (a'₁ : Int),
          (a'₁ = (DemoLayer.i l₀)) ->
           ((k1 a'₁ (DemoLayer.i l₀) (DemoLayer.o l₀) a'₀))) ∧
         (∀ (a'₂ : Int),
          ((k1 a'₂ (DemoLayer.i l₀) (DemoLayer.o l₀) a'₀)) ->
           (0 ≤ a'₂) ->
            (((DemoLayer.i l₀) = a'₂)) ∧
            ((a'₀ < (DemoLayer.o l₀))) ∧
            ((a'₀ < (DemoLayer.o l₀)))
            )
         ) ∧
      (∀ (item₀ : Int),
       ((0 ≤ item₀) ∧ (item₀ < (DemoLayer.o l₀))) ->
        ((k0 item₀ (DemoLayer.i l₀) (DemoLayer.o l₀)))) ∧
      (((k2 (DemoLayer.o l₀) (DemoLayer.i l₀) (DemoLayer.o l₀)))) ∧
      (∀ (a'₄ : Int),
       ((k2 a'₄ (DemoLayer.i l₀) (DemoLayer.o l₀))) ->
        (a'₄ = (DemoLayer.o l₀)))
      
end F
