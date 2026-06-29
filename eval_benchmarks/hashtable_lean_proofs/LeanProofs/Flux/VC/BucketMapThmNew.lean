import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapThmNew := 
 ∀ (k₀ : Int),
  (k₀ ≥ 0) ->
   (((32 * 4) ≥ 5)) ∧
   (∀ (res₀ : (BucketMapHashMap Int)),
    (¬(alist_aseq_contains_key (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots res₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots res₀)))) k₀)) ->
     (res₀ = (BucketMapHashMap.mkBucketMapHashMap₀ 0 (BucketMapFraction.mkBucketMapFraction₀ 4 5) ((32 * 4) / 5) False (bucket_map_empties (t0 := Int) 32))) ->
      ((BucketMapHashMap.max_load res₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots res₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor res₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor res₀)))) ->
       (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots res₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor res₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor res₀))) ->
        ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor res₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor res₀))) ->
         ((BucketMapHashMap.num_entries res₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots res₀))) ->
          (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots res₀)) ->
           (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots res₀)) ->
            ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots res₀)) > 0) ->
             (((32 * 4) / 5) = (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) 32)) * 4) / 5)) ->
              (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) 32)) * 4) ≥ 5) ->
               (0 = (bucket_map_total_len (t0 := Int) (bucket_map_empties (t0 := Int) 32))) ->
                (bucket_map_keys_distributed_by_hash (t0 := Int) (bucket_map_empties (t0 := Int) 32)) ->
                 (bucket_map_unique_keys (t0 := Int) (bucket_map_empties (t0 := Int) 32)) ->
                  ((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) 32)) > 0) ->
                   (¬(alist_aseq_contains_key (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots (BucketMapHashMap.mkBucketMapHashMap₀ 0 (BucketMapFraction.mkBucketMapFraction₀ 4 5) ((32 * 4) / 5) False (bucket_map_empties (t0 := Int) 32))) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots (BucketMapHashMap.mkBucketMapHashMap₀ 0 (BucketMapFraction.mkBucketMapFraction₀ 4 5) ((32 * 4) / 5) False (bucket_map_empties (t0 := Int) 32)))))) k₀)))
   
end F
