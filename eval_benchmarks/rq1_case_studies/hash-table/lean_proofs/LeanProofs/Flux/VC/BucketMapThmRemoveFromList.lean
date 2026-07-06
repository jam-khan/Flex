import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqRemoveKey
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqLen
import LeanProofs.User.Fun.AlistAseqUniqueKeys
import LeanProofs.User.Fun.AlistAseqKeysUnchangedExceptK
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapThmRemoveFromList := 
 ∀ (k₀ : Int),
  ∀ (ls₀ : (ASeq Int Int)),
   (alist_aseq_unique_keys (t0 := Int) (t1 := Int) ls₀) ->
    (k₀ ≥ 0) ->
     ∀ (ls_res₀ : (ASeq Int Int)),
      ∀ (is_some₀ : Prop),
       (is_some₀ = (alist_aseq_contains_key (t0 := Int) (t1 := Int) ls₀ k₀)) ->
        (is_some₀ -> (ls_res₀ = (alist_aseq_remove_key (t0 := Int) (t1 := Int) ls₀ k₀))) ->
         ((¬is_some₀) -> (ls_res₀ = ls₀)) ->
          ((¬(alist_aseq_contains_key (t0 := Int) (t1 := Int) ls_res₀ k₀))) ∧
          ((alist_aseq_keys_unchanged_except_k (t0 := Int) (t1 := Int) ls₀ ls_res₀ k₀)) ∧
          (((alist_aseq_len (t0 := Int) (t1 := Int) ls_res₀) = ((alist_aseq_len (t0 := Int) (t1 := Int) ls₀) - (if is_some₀ then 1 else 0))))
          
end F
