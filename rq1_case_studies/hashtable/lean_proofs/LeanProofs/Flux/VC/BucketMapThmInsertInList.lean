import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqKeyMatches
import LeanProofs.User.Fun.AlistAseqLen
import LeanProofs.User.Fun.AlistAseqUniqueKeys
import LeanProofs.User.Fun.AlistAseqKeysUnchangedExceptK
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapThmInsertInList := 
 ∀ (k₀ : Int),
  ∀ (val₀ : Int),
   ∀ (ls₀ : (ASeq Int Int)),
    (alist_aseq_unique_keys (t0 := Int) (t1 := Int) ls₀) ->
     (k₀ ≥ 0) ->
      ∀ (ls_res₀ : (ASeq Int Int)),
       ∀ (inserted₀ : Prop),
        (inserted₀ = (¬(alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ k₀))) ->
         (inserted₀ -> (ls_res₀ = (alist_aseq_cons (t0 := Int) (t1 := Int) k₀ val₀ ls₀))) ->
          ((¬inserted₀) -> (ls_res₀ = (alist_aseq_set (t0 := Int) (t1 := Int) ls₀ k₀ val₀))) ->
           ((alist_aseq_key_matches (t0 := Int) (t1 := Int) ls_res₀ k₀ val₀)) ∧
           ((alist_aseq_keys_unchanged_except_k (t0 := Int) (t1 := Int) ls₀ ls_res₀ k₀)) ∧
           (((alist_aseq_len (t0 := Int) (t1 := Int) ls_res₀) = ((alist_aseq_len (t0 := Int) (t1 := Int) ls₀) + (if (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ k₀) then 0 else 1)))) ∧
           ((alist_aseq_unique_keys (t0 := Int) (t1 := Int) ls_res₀))
           
end F
