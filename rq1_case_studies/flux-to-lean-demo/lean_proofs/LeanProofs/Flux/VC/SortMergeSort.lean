import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPerm
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical
set_option linter.unusedVariables false


namespace F



def SortMergeSort := ∃ k0 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ((VectorsAVec.len old₀) ≥ 0) ->
   ((¬((VectorsAVec.len old₀) ≤ 1)) ->
    ∀ (aux₀ : (VectorsAVec Int)),
     ((VectorsAVec.len aux₀) = 0) ->
      ((VectorsAVec.len aux₀) ≥ 0) ->
       (((k0 (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀) 0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀)))) ∧
       (∀ (aux₁ : (VectorsAVec Int)),
        ∀ (i₀ : Int),
         ((k0 (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀))) ->
          ((¬(i₀ < (VectorsAVec.len old₀))) ->
           ((((VectorsAVec.len old₀) - 1) ≥ 0)) ∧
           ((0 < (VectorsAVec.len old₀))) ∧
           (((0 ≤ ((VectorsAVec.len old₀) - 1))) ∧
           ((((VectorsAVec.len old₀) - 1) < (VectorsAVec.len old₀)))
           ) ∧
           (((VectorsAVec.len aux₁) = (VectorsAVec.len old₀))) ∧
           (∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (((VectorsAVec.len old₀) - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) 0 ((VectorsAVec.len old₀) - 1))) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              ∀ (v₁ : (VectorsAVec Int)),
               ((VectorsAVec.len v₁) ≥ 0) ->
                ((VectorsAVec.len v₁) = (VectorsAVec.len old₀)) ->
                 (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (VectorsAVec.len v₀)))
           ) ∧
          ((i₀ < (VectorsAVec.len old₀)) ->
           (∀ (a'₅ : Int),
            ((k1 a'₅ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀) (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) i₀))) ∧
           (((k1 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) i₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀) (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) i₀)) ->
            ∀ (new₀ : (VectorsAVec Int)),
             (((VectorsAVec.len new₀) = ((VectorsAVec.len aux₁) + 1)) ∧ ((VectorsAVec.elems new₀) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) i₀)))) ->
              ((VectorsAVec.len new₀) ≥ 0) ->
               ((k0 (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (i₀ + 1) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀))))
           )
          )
       ) ∧
   (((VectorsAVec.len old₀) ≤ 1) ->
    (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
    ((sort_is_sorted_between (VectorsAVec.elems old₀) 0 (VectorsAVec.len old₀)))
    )
   
end F
