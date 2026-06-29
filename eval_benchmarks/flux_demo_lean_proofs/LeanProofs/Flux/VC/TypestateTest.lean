import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypestateGpioConfig
open Classical
set_option linter.unusedVariables false


namespace F



def TypestateTest := 
 ∀ (pin₀ : TypestateGpioConfig),
  ∀ (v₀ : TypestateGpioConfig),
   ((TypestateGpioConfig.enabled v₀) = True) ->
    ((TypestateGpioConfig.enabled v₀)) ∧
    ((TypestateGpioConfig.enabled v₀)) ∧
    ((TypestateGpioConfig.enabled v₀)) ∧
    (∀ (_pin_state₀ : Prop),
     ((TypestateGpioConfig.enabled v₀)) ∧
     ((TypestateGpioConfig.enabled v₀)) ∧
     (∀ (_pin_state₁ : Prop),
      ((TypestateGpioConfig.enabled v₀)) ∧
      ((TypestateGpioConfig.enabled v₀))
      )
     )
    
end F
