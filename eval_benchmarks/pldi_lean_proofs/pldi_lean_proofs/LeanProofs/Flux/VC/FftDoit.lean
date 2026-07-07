import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def FftDoit := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 4 16))) ∧
 (∀ (i₀ : Int),
  ∀ (np₀ : Int),
   ((k0 i₀ np₀)) ->
    (i₀ ≤ 16) ->
     ((2 ≤ np₀)) ∧
     (((k0 (i₀ + 1) (np₀ * 2))))
     )
 
end F
