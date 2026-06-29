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



def SortInsert := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   (sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 (n₀ + 1) n₀) ->
    ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
     ((VectorsAVec.len old₀) ≥ 0) ->
      (n₀ ≥ 0) ->
       (((k0 n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
       (∀ (k₀ : Int),
        ∀ (a'₁ : (VectorsAVec Int)),
         ((k0 k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
          ((¬(0 < k₀)) ->
           ((k1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
          ((0 < k₀) ->
           ((k₀ < (VectorsAVec.len a'₁))) ∧
           (∀ (a'₂ : Int),
            ((k2 a'₂ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
           (((k2 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
            (((k₀ - 1) ≥ 0)) ∧
            (((k₀ - 1) < (VectorsAVec.len a'₁))) ∧
            (∀ (a'₃ : Int),
             ((k3 a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
            (((k3 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
             ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)))) ->
              ((k1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1))) ->
              (((k₀ - 1) ≥ 0)) ∧
              (((k₀ - 1) < (VectorsAVec.len a'₁))) ∧
              ((k₀ < (VectorsAVec.len a'₁))) ∧
              (((VectorsAVec.len a'₁) ≥ 0) ->
               (((k₀ - 1) ≥ 0)) ∧
               (((k0 (k₀ - 1) (let a'₄ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)); (let a'₅ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1) a'₅) k₀ a'₄))) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)))
               )
              )
             )
            )
           ) ∧
          (((k1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
           (((VectorsAVec.len a'₁) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems a'₁) 0 (n₀ + 1)))
           )
          )
       
end F
