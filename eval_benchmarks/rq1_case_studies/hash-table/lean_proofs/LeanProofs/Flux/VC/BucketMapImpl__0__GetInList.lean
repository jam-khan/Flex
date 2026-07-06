import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqKeyMatches
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__GetInList := ∃ k0 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : (ASeq Int Int)) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (ASeq Int Int)) -> (a2 : (ASeq Int Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (ASeq Int Int)) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : (ASeq Int Int)) -> (a3 : (ASeq Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (ASeq Int Int)) -> Prop, 
 ∀ (key₀ : Int),
  ∀ (ls₀ : (ASeq Int Int)),
   (key₀ ≥ 0) ->
    (((k0 ls₀ key₀ ls₀))) ∧
    (∀ (ls₁ : (ASeq Int Int)),
     ((k0 ls₁ key₀ ls₀)) ->
      (∀ (k₀ : Int),
       ∀ (t₀ : Int),
        ∀ (l₀ : (ASeq Int Int)),
         (ls₁ = (alist_aseq_cons (t0 := Int) (t1 := Int) k₀ t₀ l₀)) ->
          (k₀ ≥ 0) ->
           ((k₀ ≠ key₀) ->
            ((k0 l₀ key₀ ls₀))) ∧
           ((¬(k₀ ≠ key₀)) ->
            (((k1 key₀ ls₀ ls₁ k₀ t₀ l₀))) ∧
            (((k2 t₀ key₀ ls₀ ls₁ k₀ t₀ l₀))) ∧
            (((k1 key₀ ls₀ ls₁ k₀ t₀ l₀)) ->
             ∀ (a'₄ : Int),
              ((k2 a'₄ key₀ ls₀ ls₁ k₀ t₀ l₀)) ->
               (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ key₀) ->
                (alist_aseq_key_matches (t0 := Int) (t1 := Int) ls₀ key₀ a'₄)) ∧
            ((True = (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ key₀)))
            )
           ) ∧
      ((ls₁ = (alist_aseq_nil (t0 := Int) (t1 := Int))) ->
       (False = (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ key₀)))
      )
    
end F
