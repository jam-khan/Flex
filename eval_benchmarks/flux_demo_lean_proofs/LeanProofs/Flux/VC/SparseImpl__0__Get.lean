import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SparseCSRMatrix
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def SparseImpl__0__Get := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> Prop, 
 ∀ (self₀ : SparseCSRMatrix),
  ∀ (row₀ : Int),
   ∀ (col₀ : Int),
    (row₀ < (SparseCSRMatrix.rows self₀)) ->
     (col₀ < (SparseCSRMatrix.cols self₀)) ->
      (row₀ ≥ 0) ->
       (col₀ ≥ 0) ->
        ((SparseCSRMatrix.rows self₀) ≥ 0) ->
         ((SparseCSRMatrix.cols self₀) ≥ 0) ->
          (0 ≤ (SparseCSRMatrix.nnz self₀)) ->
           (0 ≤ ((SparseCSRMatrix.rows self₀) + 1)) ->
            ((row₀ < ((SparseCSRMatrix.rows self₀) + 1))) ∧
            (∀ (v₀ : Int),
             (v₀ ≤ (SparseCSRMatrix.nnz self₀)) ->
              ((k0 v₀ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀))) ∧
            (∀ (a'₁ : Int),
             ((k0 a'₁ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀)) ->
              (a'₁ ≥ 0) ->
               (((row₀ + 1) < ((SparseCSRMatrix.rows self₀) + 1))) ∧
               (∀ (v₁ : Int),
                (v₁ ≤ (SparseCSRMatrix.nnz self₀)) ->
                 ((k1 v₁ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁))) ∧
               (∀ (a'₃ : Int),
                ((k1 a'₃ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁)) ->
                 (a'₃ ≥ 0) ->
                  (((k2 a'₁ a'₃ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁ a'₃))) ∧
                  (∀ (iter₀ : (OpsRangeRange Int)),
                   ((k2 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁ a'₃)) ->
                    ∀ (r₀ : (OpsRangeRange Int)),
                     ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
                      (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
                       ∀ (a'₆ : Int),
                        (a'₆ = (OpsRangeRange.start iter₀)) ->
                         (a'₆ ≥ 0) ->
                          ((a'₆ < (SparseCSRMatrix.nnz self₀))) ∧
                          (∀ (v₂ : Int),
                           (v₂ < (SparseCSRMatrix.cols self₀)) ->
                            ((k3 v₂ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁ a'₃ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₆))) ∧
                          (∀ (a'₈ : Int),
                           ((k3 a'₈ (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁ a'₃ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₆)) ->
                            (a'₈ ≥ 0) ->
                             ((a'₈ ≠ col₀) ->
                              ((k2 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) (SparseCSRMatrix.rows self₀) (SparseCSRMatrix.cols self₀) (SparseCSRMatrix.nnz self₀) row₀ col₀ a'₁ a'₃))) ∧
                             ((¬(a'₈ ≠ col₀)) ->
                              (a'₆ < (SparseCSRMatrix.nnz self₀)))
                             )
                          )
                  )
               )
            
end F
