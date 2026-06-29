import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.AlistAseqRemoveKey
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqKeyMatches
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__RemoveFromList := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : (ASeq Int Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (ASeq Int Int)) -> Prop, ∃ k1 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : (ASeq Int Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (ASeq Int Int)) -> (a6 : (ASeq Int Int)) -> (a7 : Prop) -> Prop, ∃ k2 : (a0 : (ASeq Int Int)) -> (a1 : Prop) -> (a2 : Int) -> (a3 : (ASeq Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (ASeq Int Int)) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (ASeq Int Int)) -> (a2 : Prop) -> (a3 : Int) -> (a4 : (ASeq Int Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : (ASeq Int Int)) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : (ASeq Int Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (ASeq Int Int)) -> Prop, ∃ k5 : (a0 : (ASeq Int Int)) -> (a1 : Prop) -> (a2 : Int) -> (a3 : (ASeq Int Int)) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : (ASeq Int Int)) -> (a2 : Prop) -> (a3 : Int) -> (a4 : (ASeq Int Int)) -> Prop, 
 ∀ (k₀ : Int),
  ∀ (ls₀ : (ASeq Int Int)),
   (k₀ ≥ 0) ->
    (∀ (k₁ : Int),
     ∀ (t₀ : Int),
      ∀ (l₀ : (ASeq Int Int)),
       (ls₀ = (alist_aseq_cons (t0 := Int) (t1 := Int) k₁ t₀ l₀)) ->
        (k₁ ≥ 0) ->
         ((k₁ ≠ k₀) ->
          (∀ (a'₃ : Int),
           ((k0 a'₃ k₀ ls₀ k₁ t₀ l₀))) ∧
          (∀ (ls_res₀ : (ASeq Int Int)),
           ∀ (is_some₀ : Prop),
            (is_some₀ = (alist_aseq_contains_key (t0 := Int) (t1 := Int) l₀ k₀)) ->
             (is_some₀ -> (ls_res₀ = (alist_aseq_remove_key (t0 := Int) (t1 := Int) l₀ k₀))) ->
              ((¬is_some₀) -> (ls_res₀ = l₀)) ->
               (((k1 ls_res₀ k₀ ls₀ k₁ t₀ l₀ ls_res₀ is_some₀))) ∧
               (∀ (a'₆ : (ASeq Int Int)),
                ((k1 a'₆ k₀ ls₀ k₁ t₀ l₀ ls_res₀ is_some₀)) ->
                 (((k2 (alist_aseq_cons (t0 := Int) (t1 := Int) k₁ t₀ a'₆) is_some₀ k₀ ls₀ k₁ t₀ l₀))) ∧
                 (∀ (v₀ : Int),
                  (((k0 v₀ k₀ ls₀ k₁ t₀ l₀)) ∧ ((alist_aseq_contains_key (t0 := Int) (t1 := Int) l₀ k₀) -> (alist_aseq_key_matches (t0 := Int) (t1 := Int) l₀ k₀ v₀))) ->
                   ((k3 v₀ (alist_aseq_cons (t0 := Int) (t1 := Int) k₁ t₀ a'₆) is_some₀ k₀ ls₀ k₁ t₀ l₀)))
                 )
               )
          ) ∧
         ((¬(k₁ ≠ k₀)) ->
          (((k4 t₀ k₀ ls₀ k₁ t₀ l₀))) ∧
          (((k2 l₀ True k₀ ls₀ k₁ t₀ l₀))) ∧
          (∀ (a'₈ : Int),
           ((k4 a'₈ k₀ ls₀ k₁ t₀ l₀)) ->
            ((k3 a'₈ l₀ True k₀ ls₀ k₁ t₀ l₀)))
          ) ∧
         (∀ (a'₉ : (ASeq Int Int)),
          ∀ (a'₁₀ : Prop),
           ((k2 a'₉ a'₁₀ k₀ ls₀ k₁ t₀ l₀)) ->
            (((k5 a'₉ a'₁₀ k₀ ls₀))) ∧
            (∀ (a'₁₁ : Int),
             ((k3 a'₁₁ a'₉ a'₁₀ k₀ ls₀ k₁ t₀ l₀)) ->
              ((k6 a'₁₁ a'₉ a'₁₀ k₀ ls₀)))
            )
         ) ∧
    ((ls₀ = (alist_aseq_nil (t0 := Int) (t1 := Int))) ->
     ((k5 (alist_aseq_nil (t0 := Int) (t1 := Int)) False k₀ ls₀))) ∧
    (∀ (a'₁₂ : (ASeq Int Int)),
     ∀ (a'₁₃ : Prop),
      ((k5 a'₁₂ a'₁₃ k₀ ls₀)) ->
       (∀ (a'₁₄ : Int),
        ((k6 a'₁₄ a'₁₂ a'₁₃ k₀ ls₀)) ->
         (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ k₀) ->
          (alist_aseq_key_matches (t0 := Int) (t1 := Int) ls₀ k₀ a'₁₄)) ∧
       ((a'₁₃ = (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ k₀))) ∧
       (a'₁₃ ->
        (a'₁₂ = (alist_aseq_remove_key (t0 := Int) (t1 := Int) ls₀ k₀))) ∧
       ((¬a'₁₃) ->
        (a'₁₂ = ls₀))
       )
    
end F
