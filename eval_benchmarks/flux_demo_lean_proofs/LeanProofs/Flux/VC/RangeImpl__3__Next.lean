import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RangeUsizeRange
open Classical
set_option linter.unusedVariables false


namespace F



def RangeImpl__3__Next := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (old₀ : RangeUsizeRange),
  ((RangeUsizeRange.start old₀) ≥ 0) ->
   ((RangeUsizeRange.end_ old₀) ≥ 0) ->
    ((¬((RangeUsizeRange.start old₀) ≥ (RangeUsizeRange.end_ old₀))) ->
     (((k0 (RangeUsizeRange.start old₀) (RangeUsizeRange.start old₀) (RangeUsizeRange.end_ old₀)))) ∧
     (∀ (a'₀ : Int),
      ((k0 a'₀ (RangeUsizeRange.start old₀) (RangeUsizeRange.end_ old₀))) ->
       (a'₀ = (RangeUsizeRange.start old₀))) ∧
     ((True = ((RangeUsizeRange.start old₀) < (RangeUsizeRange.end_ old₀)))) ∧
     ((((RangeUsizeRange.start old₀) < (RangeUsizeRange.end_ old₀)) ->
      (((RangeUsizeRange.start old₀) + 1) = ((RangeUsizeRange.start old₀) + 1))) ∧
     (((RangeUsizeRange.end_ old₀) = (RangeUsizeRange.end_ old₀)))
     )
     ) ∧
    (((RangeUsizeRange.start old₀) ≥ (RangeUsizeRange.end_ old₀)) ->
     ((False = ((RangeUsizeRange.start old₀) < (RangeUsizeRange.end_ old₀)))) ∧
     ((((RangeUsizeRange.start old₀) < (RangeUsizeRange.end_ old₀)) ->
      ((RangeUsizeRange.start old₀) = ((RangeUsizeRange.start old₀) + 1))) ∧
     (((RangeUsizeRange.end_ old₀) = (RangeUsizeRange.end_ old₀)))
     )
     )
    
end F
