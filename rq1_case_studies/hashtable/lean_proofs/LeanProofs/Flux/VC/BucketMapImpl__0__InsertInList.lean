import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqContainsKey
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__InsertInList := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : (ASeq Int Int)) -> Prop, ∃ k1 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (ASeq Int Int)) -> (a4 : (ASeq Int Int)) -> (a5 : Prop) -> Prop, ∃ k2 : (a0 : (ASeq Int Int)) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> (a4 : (ASeq Int Int)) -> (a5 : (ASeq Int Int)) -> (a6 : Prop) -> Prop, 
 ∀ (key₀ : Int),
  ∀ (val₀ : Int),
   ∀ (ls₀ : (ASeq Int Int)),
    (key₀ ≥ 0) ->
     (∀ (a'₀ : Int),
      ((k0 a'₀ key₀ val₀ ls₀))) ∧
     (((k0 val₀ key₀ val₀ ls₀))) ∧
     (∀ (new_slf₀ : (ASeq Int Int)),
      ∀ (is_some₀ : Prop),
       (is_some₀ = (¬(alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ key₀))) ->
        (is_some₀ -> (new_slf₀ = ls₀)) ->
         ((¬is_some₀) -> (new_slf₀ = (alist_aseq_set (t0 := Int) (t1 := Int) ls₀ key₀ val₀))) ->
          ((is_some₀ = True) ->
           ((k0 val₀ key₀ val₀ ls₀)) ->
            (((k1 new_slf₀ key₀ val₀ ls₀ new_slf₀ is_some₀))) ∧
            (∀ (a'₃ : (ASeq Int Int)),
             ((k1 a'₃ key₀ val₀ ls₀ new_slf₀ is_some₀)) ->
              ((k2 (alist_aseq_cons (t0 := Int) (t1 := Int) key₀ val₀ a'₃) True key₀ val₀ ls₀ new_slf₀ is_some₀)))
            ) ∧
          ((is_some₀ = False) ->
           ((k2 new_slf₀ False key₀ val₀ ls₀ new_slf₀ is_some₀))) ∧
          (∀ (a'₄ : (ASeq Int Int)),
           ∀ (a'₅ : Prop),
            ((k2 a'₄ a'₅ key₀ val₀ ls₀ new_slf₀ is_some₀)) ->
             ((a'₅ = (¬(alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ key₀)))) ∧
             (a'₅ ->
              (a'₄ = (alist_aseq_cons (t0 := Int) (t1 := Int) key₀ val₀ ls₀))) ∧
             ((¬a'₅) ->
              (a'₄ = (alist_aseq_set (t0 := Int) (t1 := Int) ls₀ key₀ val₀)))
             )
          )
     
end F
