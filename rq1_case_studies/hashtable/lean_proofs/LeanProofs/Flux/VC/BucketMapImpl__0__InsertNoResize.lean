import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.SvecSet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__InsertNoResize := ∃ k0 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : (OVec (ASeq Int Int))) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : (OVec (ASeq Int Int))) -> (a7 : Int) -> (a8 : Int) -> (a9 : (ASeq Int Int)) -> (a10 : Prop) -> Prop, 
 ∀ (slf₀ : (BucketMapHashMap Int)),
  ∀ (key₀ : Int),
   ∀ (value₀ : Int),
    ((BucketMapHashMap.max_load slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ->
     (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
      ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
       ((BucketMapHashMap.num_entries slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots slf₀))) ->
        (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots slf₀)) ->
         (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots slf₀)) ->
          ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) > 0) ->
           (key₀ ≥ 0) ->
            ((BucketMapHashMap.num_entries slf₀) ≥ 0) ->
             ((BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) ≠ 0) ->
              ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) ≠ 0) ->
               ((BucketMapHashMap.max_load slf₀) ≥ 0) ->
                ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≥ 0) ->
                 (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≠ 0)) ∧
                 (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≠ 0) ->
                  (((key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) < (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) ∧
                  (∀ (a'₀ : (ASeq Int Int)),
                   ((k0 a'₀ (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ value₀))) ∧
                  (((k0 (alist_aseq_nil (t0 := Int) (t1 := Int)) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ value₀))) ∧
                  (((k0 (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ value₀)) ->
                   ∀ (ls_res₀ : (ASeq Int Int)),
                    ∀ (inserted₀ : Prop),
                     (inserted₀ = (¬(alist_aseq_contains_key (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) key₀))) ->
                      (inserted₀ -> (ls_res₀ = (alist_aseq_cons (t0 := Int) (t1 := Int) key₀ value₀ (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))))))) ->
                       ((¬inserted₀) -> (ls_res₀ = (alist_aseq_set (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) key₀ value₀))) ->
                        (((key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) < (svec_len (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int)))))) ∧
                        ((¬inserted₀) ->
                         ((k1 (BucketMapHashMap.num_entries slf₀) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ value₀ ls_res₀ inserted₀))) ∧
                        (inserted₀ ->
                         ((k1 ((BucketMapHashMap.num_entries slf₀) + 1) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ value₀ ls_res₀ True))) ∧
                        (∀ (a'₃ : Int),
                         ((k1 a'₃ (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ value₀ ls_res₀ inserted₀)) ->
                          (((BucketMapHashMap.max_load slf₀) = (((svec_len (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))))) ∧
                          ((((svec_len (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ∧
                          ((a'₃ = (bucket_map_total_len (t0 := Int) (svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀)))) ∧
                          ((bucket_map_keys_distributed_by_hash (t0 := Int) (svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀))) ∧
                          ((bucket_map_unique_keys (t0 := Int) (svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀))) ∧
                          (((svec_len (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀)) > 0)) ∧
                          ((a'₃ = ((BucketMapHashMap.num_entries slf₀) + (if (alist_aseq_contains_key (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) key₀) then 0 else 1)))) ∧
                          (((svec_set (t0 := (ASeq Int Int)) (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) (alist_aseq_nil (t0 := Int) (t1 := Int))) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀))) ls_res₀) = (let a'₄ := (key₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀))); (let a'₅ := (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀) a'₄); (let a'₆ := (alist_aseq_contains_key (t0 := Int) (t1 := _) a'₅ key₀); (svec_set (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀) a'₄ (if a'₆ then (alist_aseq_set (t0 := Int) (t1 := _) a'₅ key₀ value₀) else (alist_aseq_cons (t0 := Int) (t1 := _) key₀ value₀ a'₅))))))))
                          )
                        )
                  )
                 
end F
