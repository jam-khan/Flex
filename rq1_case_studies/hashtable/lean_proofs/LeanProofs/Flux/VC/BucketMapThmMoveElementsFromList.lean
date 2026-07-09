import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqKeyMatches
import LeanProofs.User.Fun.AlistAseqLen
import LeanProofs.User.Fun.AlistAseqUniqueKeys
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapAbsorbBucket
import LeanProofs.User.Fun.BucketMapDisjointWithList
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapThmMoveElementsFromList := 
 ∀ (hm₀ : (BucketMapHashMap Int)),
  ∀ (ls₀ : (ASeq Int Int)),
   ∀ (k₀ : Int),
    ∀ (v₀ : Int),
     (bucket_map_disjoint_with_list (t0 := Int) (BucketMapHashMap.slots hm₀) ls₀) ->
      (alist_aseq_unique_keys (t0 := Int) (t1 := Int) ls₀) ->
       ((BucketMapHashMap.max_load hm₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀)))) ->
        (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀))) ->
         ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀))) ->
          ((BucketMapHashMap.num_entries hm₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots hm₀))) ->
           (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots hm₀)) ->
            (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots hm₀)) ->
             ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) > 0) ->
              (k₀ ≥ 0) ->
               ∀ (new_t₀ : (BucketMapHashMap Int)),
                ((BucketMapHashMap.max_load new_t₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀)))) ->
                 (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀))) ->
                  ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀))) ->
                   ((BucketMapHashMap.num_entries new_t₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_t₀))) ->
                    (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_t₀)) ->
                     (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_t₀)) ->
                      ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) > 0) ->
                       ((BucketMapHashMap.max_load new_t₀) = (BucketMapHashMap.max_load hm₀)) ->
                        ((BucketMapHashMap.max_load_factor new_t₀) = (BucketMapHashMap.max_load_factor hm₀)) ->
                         ((BucketMapHashMap.saturated new_t₀) = (BucketMapHashMap.saturated hm₀)) ->
                          ((BucketMapHashMap.num_entries new_t₀) ≥ (BucketMapHashMap.num_entries hm₀)) ->
                           ((BucketMapHashMap.num_entries new_t₀) ≤ ((BucketMapHashMap.num_entries hm₀) + (alist_aseq_len (t0 := Int) (t1 := Int) ls₀))) ->
                            ((BucketMapHashMap.slots new_t₀) = (bucket_map_absorb_bucket (t0 := Int) (BucketMapHashMap.slots hm₀) ls₀)) ->
                             ((alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_t₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_t₀)))) k₀ v₀) ->
                              ((alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀)))) k₀ v₀) ∨ (alist_aseq_key_matches (t0 := Int) (t1 := Int) ls₀ k₀ v₀))) ∧
                             ((alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀)))) k₀ v₀) ->
                              (alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_t₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_t₀)))) k₀ v₀)) ∧
                             ((alist_aseq_key_matches (t0 := Int) (t1 := Int) ls₀ k₀ v₀) ->
                              (alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_t₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_t₀)))) k₀ v₀)) ∧
                             (((BucketMapHashMap.num_entries new_t₀) = ((BucketMapHashMap.num_entries hm₀) + (alist_aseq_len (t0 := Int) (t1 := Int) ls₀))))
                             
end F
