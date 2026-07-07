import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RangeI32Range
open Classical
set_option linter.unusedVariables false


namespace F



def RangeImpl__4__Next := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (old₀ : RangeI32Range),
  ((¬((RangeI32Range.start old₀) ≥ (RangeI32Range.end_ old₀))) ->
   (((k0 (RangeI32Range.start old₀) (RangeI32Range.start old₀) (RangeI32Range.end_ old₀)))) ∧
   (∀ (a'₀ : Int),
    ((k0 a'₀ (RangeI32Range.start old₀) (RangeI32Range.end_ old₀))) ->
     (a'₀ = (RangeI32Range.start old₀))) ∧
   ((True = ((RangeI32Range.start old₀) < (RangeI32Range.end_ old₀)))) ∧
   ((((RangeI32Range.start old₀) < (RangeI32Range.end_ old₀)) ->
    (((RangeI32Range.start old₀) + 1) = ((RangeI32Range.start old₀) + 1))) ∧
   (((RangeI32Range.end_ old₀) = (RangeI32Range.end_ old₀)))
   )
   ) ∧
  (((RangeI32Range.start old₀) ≥ (RangeI32Range.end_ old₀)) ->
   ((False = ((RangeI32Range.start old₀) < (RangeI32Range.end_ old₀)))) ∧
   ((((RangeI32Range.start old₀) < (RangeI32Range.end_ old₀)) ->
    ((RangeI32Range.start old₀) = ((RangeI32Range.start old₀) + 1))) ∧
   (((RangeI32Range.end_ old₀) = (RangeI32Range.end_ old₀)))
   )
   )
  
end F
