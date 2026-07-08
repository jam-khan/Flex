import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.AlistAseqContainsKey
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__ContainsKeyInList := ∃ k0 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : (ASeq Int Int)) -> Prop, 
 ∀ (k₀ : Int),
  ∀ (l₀ : (ASeq Int Int)),
   (k₀ ≥ 0) ->
    (((k0 l₀ k₀ l₀))) ∧
    (∀ (ls₀ : (ASeq Int Int)),
     ((k0 ls₀ k₀ l₀)) ->
      (∀ (k₁ : Int),
       ∀ (t₀ : Int),
        ∀ (l₁ : (ASeq Int Int)),
         (ls₀ = (alist_aseq_cons (t0 := Int) (t1 := Int) k₁ t₀ l₁)) ->
          (k₁ ≥ 0) ->
           ((k₁ ≠ k₀) ->
            ((k0 l₁ k₀ l₀))) ∧
           ((¬(k₁ ≠ k₀)) ->
            (True = (alist_aseq_contains_key (t0 := Int) (t1 := Int) l₀ k₀)))
           ) ∧
      ((ls₀ = (alist_aseq_nil (t0 := Int) (t1 := Int))) ->
       (False = (alist_aseq_contains_key (t0 := Int) (t1 := Int) l₀ k₀)))
      )
    
end F
