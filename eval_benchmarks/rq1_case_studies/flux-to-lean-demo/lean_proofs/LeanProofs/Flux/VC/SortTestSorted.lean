import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.VectorsArrGet
open Classical
set_option linter.unusedVariables false


namespace F



def SortTestSorted := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> Prop, 
 ∀ (me₀ : (VectorsAVec Int)),
  ((VectorsAVec.len me₀) ≥ 0) ->
   ((sort_is_sorted_between (VectorsAVec.elems me₀) 0 (VectorsAVec.len me₀)) ∧ (100 < (VectorsAVec.len me₀))) ->
    ((0 < (VectorsAVec.len me₀))) ∧
    (∀ (a'₀ : Int),
     ((k0 a'₀ (VectorsAVec.elems me₀) (VectorsAVec.len me₀)))) ∧
    (((k0 (vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 0) (VectorsAVec.elems me₀) (VectorsAVec.len me₀))) ->
     ((1 < (VectorsAVec.len me₀))) ∧
     (∀ (a'₁ : Int),
      ((k1 a'₁ (VectorsAVec.elems me₀) (VectorsAVec.len me₀)))) ∧
     (((k1 (vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 1) (VectorsAVec.elems me₀) (VectorsAVec.len me₀))) ->
      (((vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 0) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 1)) = True))
     )
    
end F
