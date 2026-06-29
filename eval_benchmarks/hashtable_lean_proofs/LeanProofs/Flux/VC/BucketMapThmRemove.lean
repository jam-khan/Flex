import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqRemoveKey
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



def BucketMapThmRemove := 
 ∀ (hm₀ : (BucketMapHashMap Int)),
  ∀ (k₀ : Int),
   ((BucketMapHashMap.max_load hm₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀)))) ->
    (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀))) ->
     ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀))) ->
      ((BucketMapHashMap.num_entries hm₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots hm₀))) ->
       (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots hm₀)) ->
        (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots hm₀)) ->
         ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) > 0) ->
          (k₀ ≥ 0) ->
           ∀ (is_some₀ : Prop),
            ∀ (new_slf₀ : (BucketMapHashMap Int)),
             ((BucketMapHashMap.max_load new_slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)))) ->
              (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
               ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
                ((BucketMapHashMap.num_entries new_slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_slf₀))) ->
                 (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                  (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                   ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) > 0) ->
                    (is_some₀ = (alist_aseq_contains_key (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)))) k₀)) ->
                     ((BucketMapHashMap.num_entries new_slf₀) = ((BucketMapHashMap.num_entries hm₀) - (if is_some₀ then 1 else 0))) ->
                      ((BucketMapHashMap.max_load new_slf₀) = (BucketMapHashMap.max_load hm₀)) ->
                       ((BucketMapHashMap.max_load_factor new_slf₀) = (BucketMapHashMap.max_load_factor hm₀)) ->
                        ((BucketMapHashMap.saturated new_slf₀) = (BucketMapHashMap.saturated hm₀)) ->
                         ((BucketMapHashMap.slots new_slf₀) = (if is_some₀ then (svec_set (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀))) (alist_aseq_remove_key (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)))) k₀)) else (BucketMapHashMap.slots hm₀))) ->
                          ((is_some₀ = (alist_aseq_contains_key (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀)))) k₀))) ∧
                          ((¬(alist_aseq_contains_key (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_slf₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_slf₀)))) k₀)))
                          
end F
