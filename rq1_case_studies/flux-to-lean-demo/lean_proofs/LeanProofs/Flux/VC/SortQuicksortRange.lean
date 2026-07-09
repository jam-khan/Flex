import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPartitionedBy
import LeanProofs.User.Fun.SortIsPerm
open Classical
set_option linter.unusedVariables false


namespace F



def SortQuicksortRange := ∃ k0 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     (hi₀ < (VectorsAVec.len old₀)) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         ((¬(lo₀ < hi₀)) ->
          (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
          ((sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (hi₀ + 1))) ∧
          ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems old₀) lo₀ hi₀))
          ) ∧
         ((lo₀ < hi₀) ->
          ∀ (p₀ : Int),
           ∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_partitioned_by (VectorsAVec.elems v₀) lo₀ p₀ (hi₀ + 1) p₀) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) lo₀ hi₀) ∧ (lo₀ ≤ p₀) ∧ (p₀ ≤ hi₀)) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              (p₀ ≥ 0) ->
               ((¬(lo₀ < p₀)) ->
                ((k0 (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
               ((lo₀ < p₀) ->
                (((p₀ - 1) ≥ 0)) ∧
                ((lo₀ < (VectorsAVec.len v₀))) ∧
                (((p₀ - 1) < (VectorsAVec.len v₀))) ∧
                (∀ (v₁ : (VectorsAVec Int)),
                 (((VectorsAVec.len v₁) = (VectorsAVec.len v₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₁) lo₀ ((p₀ - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₀) (VectorsAVec.elems v₁) lo₀ (p₀ - 1))) ->
                  ((VectorsAVec.len v₁) ≥ 0) ->
                   ((k0 (VectorsAVec.elems v₁) (VectorsAVec.len v₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))))
                ) ∧
               (∀ (a'₃ : (VectorsAVec Int)),
                ((k0 (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                 ((¬(p₀ < hi₀)) ->
                  (((VectorsAVec.len a'₃) = (VectorsAVec.len old₀))) ∧
                  ((sort_is_sorted_between (VectorsAVec.elems a'₃) lo₀ (hi₀ + 1))) ∧
                  ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems a'₃) lo₀ hi₀))
                  ) ∧
                 ((p₀ < hi₀) ->
                  (((p₀ + 1) < (VectorsAVec.len a'₃))) ∧
                  ((hi₀ < (VectorsAVec.len a'₃))) ∧
                  (∀ (v₂ : (VectorsAVec Int)),
                   (((VectorsAVec.len v₂) = (VectorsAVec.len a'₃)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₂) (p₀ + 1) (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems a'₃) (VectorsAVec.elems v₂) (p₀ + 1) hi₀)) ->
                    ((VectorsAVec.len v₂) ≥ 0) ->
                     (((VectorsAVec.len v₂) = (VectorsAVec.len old₀))) ∧
                     ((sort_is_sorted_between (VectorsAVec.elems v₂) lo₀ (hi₀ + 1))) ∧
                     ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₂) lo₀ hi₀))
                     )
                  )
                 )
               )
         
end F
