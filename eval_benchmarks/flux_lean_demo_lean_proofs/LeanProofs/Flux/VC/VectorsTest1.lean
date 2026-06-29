import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsTest1 := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> Prop, 
 ∀ (v₀ : (VectorsAVec Int)),
  ((VectorsAVec.len v₀) = 0) ->
   ((VectorsAVec.len v₀) ≥ 0) ->
    (((k0 10 (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
    (∀ (new₀ : (VectorsAVec Int)),
     (((VectorsAVec.len new₀) = ((VectorsAVec.len v₀) + 1)) ∧ ((VectorsAVec.elems new₀) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems v₀) (VectorsAVec.len v₀) 10))) ->
      ((VectorsAVec.len new₀) ≥ 0) ->
       (∀ (a'₂ : Int),
        ((k0 a'₂ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
         ((k1 a'₂ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀)))) ∧
       (((k1 20 (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀)))) ∧
       (∀ (new₁ : (VectorsAVec Int)),
        (((VectorsAVec.len new₁) = ((VectorsAVec.len new₀) + 1)) ∧ ((VectorsAVec.elems new₁) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) 20))) ->
         ((VectorsAVec.len new₁) ≥ 0) ->
          (∀ (a'₄ : Int),
           ((k1 a'₄ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀))) ->
            ((k2 a'₄ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁)))) ∧
          (((k2 30 (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁)))) ∧
          (∀ (new₂ : (VectorsAVec Int)),
           (((VectorsAVec.len new₂) = ((VectorsAVec.len new₁) + 1)) ∧ ((VectorsAVec.elems new₂) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) 30))) ->
            ((VectorsAVec.len new₂) ≥ 0) ->
             ((0 < (VectorsAVec.len new₂))) ∧
             (∀ (a'₆ : Int),
              ((k2 a'₆ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁))) ->
               ((k3 a'₆ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) (VectorsAVec.elems new₂) (VectorsAVec.len new₂)))) ∧
             (((k3 (vectors_arr_get (t0 := Int) (VectorsAVec.elems new₂) 0) (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) (VectorsAVec.elems new₂) (VectorsAVec.len new₂))) ->
              ((((vectors_arr_get (t0 := Int) (VectorsAVec.elems new₂) 0) = 10) = True)) ∧
              ((1 < (VectorsAVec.len new₂))) ∧
              (∀ (a'₇ : Int),
               ((k2 a'₇ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁))) ->
                ((k4 a'₇ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) (VectorsAVec.elems new₂) (VectorsAVec.len new₂)))) ∧
              (((k4 (vectors_arr_get (t0 := Int) (VectorsAVec.elems new₂) 1) (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) (VectorsAVec.elems new₂) (VectorsAVec.len new₂))) ->
               ((((vectors_arr_get (t0 := Int) (VectorsAVec.elems new₂) 1) = 20) = True)) ∧
               ((2 < (VectorsAVec.len new₂))) ∧
               (∀ (a'₈ : Int),
                ((k2 a'₈ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁))) ->
                 ((k5 a'₈ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) (VectorsAVec.elems new₂) (VectorsAVec.len new₂)))) ∧
               (((k5 (vectors_arr_get (t0 := Int) (VectorsAVec.elems new₂) 2) (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) (VectorsAVec.elems new₂) (VectorsAVec.len new₂))) ->
                (((vectors_arr_get (t0 := Int) (VectorsAVec.elems new₂) 2) = 30) = True))
               )
              )
             )
          )
       )
    
end F
