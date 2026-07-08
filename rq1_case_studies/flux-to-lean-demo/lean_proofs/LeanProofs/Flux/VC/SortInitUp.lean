import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.VectorsArrSet
open Classical
set_option linter.unusedVariables false


namespace F



def SortInitUp := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ((VectorsAVec.len old₀) ≥ 0) ->
   (((k0 0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀)))) ∧
   (∀ (i₀ : Int),
    ∀ (a'₁ : (VectorsAVec Int)),
     ((k0 i₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀))) ->
      ((¬(i₀ < (VectorsAVec.len old₀))) ->
       (sort_is_sorted_between (VectorsAVec.elems a'₁) 0 (VectorsAVec.len a'₁))) ∧
      ((i₀ < (VectorsAVec.len old₀)) ->
       ((i₀ < (VectorsAVec.len a'₁))) ∧
       (((VectorsAVec.len a'₁) ≥ 0) ->
        ((k0 (i₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₁) i₀ i₀) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀))))
       )
      )
   
end F
