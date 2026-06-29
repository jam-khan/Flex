import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical
set_option linter.unusedVariables false


namespace F



def SortInsertRec := ∃ k0 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   ∀ (k₀ : Int),
    (sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 (n₀ + 1) k₀) ->
     ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
      (k₀ ≤ n₀) ->
       ((VectorsAVec.len old₀) ≥ 0) ->
        (n₀ ≥ 0) ->
         (k₀ ≥ 0) ->
          ((¬(0 < k₀)) ->
           ((k0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
          ((0 < k₀) ->
           ((k₀ < (VectorsAVec.len old₀))) ∧
           (∀ (a'₀ : Int),
            ((k1 a'₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
           (((k1 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
            (((k₀ - 1) ≥ 0)) ∧
            (((k₀ - 1) < (VectorsAVec.len old₀))) ∧
            (∀ (a'₁ : Int),
             ((k2 a'₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
            (((k2 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
             ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1)))) ->
              ((k0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1))) ->
              (((k₀ - 1) ≥ 0)) ∧
              (((k₀ - 1) < (VectorsAVec.len old₀))) ∧
              (∀ (a'₂ : Int),
               ((k3 a'₂ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
              (((k3 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
               (((k₀ - 1) ≥ 0)) ∧
               ((k₀ < (VectorsAVec.len old₀))) ∧
               (∀ (a'₃ : Int),
                ((k4 a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
               (((k4 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
                (((k₀ - 1) < (VectorsAVec.len old₀))) ∧
                (((k₀ < (VectorsAVec.len old₀))) ∧
                ((((k₀ - 1) ≥ 0)) ∧
                ((sort_is_sorted_between_exc (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1) (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀)) k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1))) 0 (n₀ + 1) (k₀ - 1))) ∧
                (((k₀ - 1) ≤ n₀))
                )
                )
                )
               )
              )
             )
            )
           ) ∧
          (((k0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
           (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems old₀) 0 (n₀ + 1)))
           )
          
end F
