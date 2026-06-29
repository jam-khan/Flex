import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPerm
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
import LeanProofs.User.Fun.VectorsArrEqBetween
open Classical
set_option linter.unusedVariables false


namespace F



def SortMerge := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (Arr Int)) -> (a11 : Int) -> (a12 : Int) -> (a13 : (Arr Int)) -> (a14 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : (Arr Int)) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k11 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (mid₀ : Int),
    ∀ (hi₀ : Int),
     ∀ (v₀ : (VectorsAVec Int)),
      (sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (mid₀ + 1)) ->
       (sort_is_sorted_between (VectorsAVec.elems old₀) (mid₀ + 1) (hi₀ + 1)) ->
        ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ->
         (lo₀ < (VectorsAVec.len old₀)) ->
          ((lo₀ ≤ mid₀) ∧ (mid₀ < (VectorsAVec.len old₀))) ->
           ((mid₀ < hi₀) ∧ (hi₀ < (VectorsAVec.len old₀))) ->
            ((VectorsAVec.len old₀) ≥ 0) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              (lo₀ ≥ 0) ->
               (mid₀ ≥ 0) ->
                (hi₀ ≥ 0) ->
                 (((k0 lo₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
                 (∀ (a'₁ : Int),
                  ((k1 a'₁ lo₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
                 (∀ (k₀ : Int),
                  ∀ (a'₃ : (VectorsAVec Int)),
                   ((k0 k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                    ((¬(k₀ ≤ hi₀)) ->
                     (((k2 lo₀ (mid₀ + 1) lo₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                     (∀ (a'₄ : Int),
                      ((k1 a'₄ k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                       ((k3 a'₄ lo₀ (mid₀ + 1) lo₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                     (∀ (i₀ : Int),
                      ∀ (j₀ : Int),
                       ∀ (out₀ : Int),
                        ∀ (a'₈ : (VectorsAVec Int)),
                         ((k2 i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                          ((¬(out₀ ≤ hi₀)) ->
                           ((((VectorsAVec.len a'₈) = (VectorsAVec.len old₀))) ∧
                           ((sort_is_sorted_between (VectorsAVec.elems a'₈) lo₀ (hi₀ + 1))) ∧
                           ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems a'₈) lo₀ hi₀))
                           ) ∧
                           ((((VectorsAVec.len a'₃) = (VectorsAVec.len old₀))) ∧
                           ((vectors_arr_eq_between (t0 := Int) (VectorsAVec.elems old₀) (VectorsAVec.elems a'₃) lo₀ (hi₀ + 1)))
                           )
                           ) ∧
                          ((out₀ ≤ hi₀) ->
                           ((¬(i₀ > mid₀)) ->
                            ((¬(j₀ > hi₀)) ->
                             ((j₀ < (VectorsAVec.len a'₃))) ∧
                             (∀ (a'₉ : Int),
                              ((k3 a'₉ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                               ((k4 a'₉ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈)))) ∧
                             (((k4 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈))) ->
                              ((i₀ < (VectorsAVec.len a'₃))) ∧
                              (∀ (a'₁₀ : Int),
                               ((k3 a'₁₀ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                ((k5 a'₁₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈)))) ∧
                              (((k5 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈))) ->
                               ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀))) ->
                                ((i₀ < (VectorsAVec.len a'₃))) ∧
                                (∀ (a'₁₁ : Int),
                                 ((k3 a'₁₁ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                  ((k6 a'₁₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈)))) ∧
                                (((k6 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈))) ->
                                 ((out₀ < (VectorsAVec.len a'₈))) ∧
                                 (((VectorsAVec.len a'₈) ≥ 0) ->
                                  (((k2 (i₀ + 1) j₀ (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                                  (∀ (a'₁₂ : Int),
                                   ((k3 a'₁₂ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                    ((k3 a'₁₂ (i₀ + 1) j₀ (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                                  )
                                 )
                                ) ∧
                               (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀)) ->
                                ((j₀ < (VectorsAVec.len a'₃))) ∧
                                (∀ (a'₁₃ : Int),
                                 ((k3 a'₁₃ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                  ((k7 a'₁₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈)))) ∧
                                (((k7 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈))) ->
                                 ((out₀ < (VectorsAVec.len a'₈))) ∧
                                 (((VectorsAVec.len a'₈) ≥ 0) ->
                                  (((k2 i₀ (j₀ + 1) (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                                  (∀ (a'₁₄ : Int),
                                   ((k3 a'₁₄ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                    ((k3 a'₁₄ i₀ (j₀ + 1) (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                                  )
                                 )
                                )
                               )
                              )
                             ) ∧
                            ((j₀ > hi₀) ->
                             ((i₀ < (VectorsAVec.len a'₃))) ∧
                             (∀ (a'₁₅ : Int),
                              ((k3 a'₁₅ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                               ((k8 a'₁₅ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈)))) ∧
                             (((k8 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈))) ->
                              ((out₀ < (VectorsAVec.len a'₈))) ∧
                              (((VectorsAVec.len a'₈) ≥ 0) ->
                               (((k2 (i₀ + 1) j₀ (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                               (∀ (a'₁₆ : Int),
                                ((k3 a'₁₆ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                 ((k3 a'₁₆ (i₀ + 1) j₀ (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                               )
                              )
                             )
                            ) ∧
                           ((i₀ > mid₀) ->
                            ((j₀ < (VectorsAVec.len a'₃))) ∧
                            (∀ (a'₁₇ : Int),
                             ((k3 a'₁₇ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                              ((k9 a'₁₇ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈)))) ∧
                            (((k9 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈))) ->
                             ((out₀ < (VectorsAVec.len a'₈))) ∧
                             (((VectorsAVec.len a'₈) ≥ 0) ->
                              (((k2 i₀ (j₀ + 1) (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                              (∀ (a'₁₈ : Int),
                               ((k3 a'₁₈ i₀ j₀ out₀ (VectorsAVec.elems a'₈) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                                ((k3 a'₁₈ i₀ (j₀ + 1) (out₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₈) out₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀)) (VectorsAVec.len a'₈) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                              )
                             )
                            )
                           )
                          )
                     ) ∧
                    ((k₀ ≤ hi₀) ->
                     ((k₀ < (VectorsAVec.len old₀))) ∧
                     (∀ (a'₁₉ : Int),
                      ((k10 a'₁₉ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                     (((k10 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                      ((k₀ < (VectorsAVec.len a'₃))) ∧
                      (∀ (a'₂₀ : Int),
                       ((k1 a'₂₀ k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                        ((k11 a'₂₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                      (((k11 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                      (((VectorsAVec.len a'₃) ≥ 0) ->
                       (((k0 (k₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀)) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
                       (∀ (a'₂₁ : Int),
                        ((k11 a'₂₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) k₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                         ((k1 a'₂₁ (k₀ + 1) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀)) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ mid₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))))
                       )
                      )
                     )
                    )
                 
end F
