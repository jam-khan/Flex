import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsPartitionedBy
import LeanProofs.User.Fun.SortIsPerm
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical
set_option linter.unusedVariables false


namespace F



def SortPartition := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     ((lo₀ < hi₀) ∧ (hi₀ < (VectorsAVec.len old₀))) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         (∀ (a'₀ : Int),
          ((k0 a'₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀))) ∧
         (((k0 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->
          (((k1 lo₀ lo₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀))) ∧
          (∀ (i₀ : Int),
           ∀ (j₀ : Int),
            ∀ (a'₃ : (VectorsAVec Int)),
             ((k1 i₀ j₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->
              ((¬(j₀ < hi₀)) ->
               ((i₀ < (VectorsAVec.len a'₃))) ∧
               ((hi₀ < (VectorsAVec.len a'₃))) ∧
               (((VectorsAVec.len a'₃) ≥ 0) ->
                (((VectorsAVec.len a'₃) = (VectorsAVec.len old₀))) ∧
                ((sort_is_partitioned_by (let a'₄ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀); (let a'₅ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) hi₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) i₀ a'₅) hi₀ a'₄))) lo₀ i₀ (hi₀ + 1) i₀)) ∧
                ((sort_is_perm (VectorsAVec.elems old₀) (let a'₆ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀); (let a'₇ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) hi₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) i₀ a'₇) hi₀ a'₆))) lo₀ hi₀)) ∧
                ((lo₀ ≤ i₀)) ∧
                ((i₀ ≤ hi₀))
                )
               ) ∧
              ((j₀ < hi₀) ->
               ((j₀ < (VectorsAVec.len a'₃))) ∧
               (∀ (a'₈ : Int),
                ((k2 a'₈ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ i₀ j₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
               (((k2 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ i₀ j₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀))) ->
                 ((k3 i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ i₀ j₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀)) ->
                 ((i₀ < (VectorsAVec.len a'₃))) ∧
                 ((j₀ < (VectorsAVec.len a'₃))) ∧
                 (((VectorsAVec.len a'₃) ≥ 0) ->
                  ((k3 (i₀ + 1) (let a'₉ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀); (let a'₁₀ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) i₀ a'₁₀) j₀ a'₉))) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ i₀ j₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                 ) ∧
                (∀ (i₁ : Int),
                 ∀ (a'₁₂ : (VectorsAVec Int)),
                  ((k3 i₁ (VectorsAVec.elems a'₁₂) (VectorsAVec.len a'₁₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ i₀ j₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                   ((k1 i₁ (j₀ + 1) (VectorsAVec.elems a'₁₂) (VectorsAVec.len a'₁₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)))
                )
               )
              )
          )
         
end F
