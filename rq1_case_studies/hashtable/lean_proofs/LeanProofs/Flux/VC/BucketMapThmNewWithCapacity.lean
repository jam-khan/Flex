import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.Flux.Struct.BucketMapHashMap
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



def BucketMapThmNewWithCapacity := 
 ∀ (capacity₀ : Int),
  ∀ (max_load_factor₀ : BucketMapFraction),
   ∀ (k₀ : Int),
    ((capacity₀ > 0) ∧ ((capacity₀ * (BucketMapFraction.dividend max_load_factor₀)) ≥ (BucketMapFraction.divisor max_load_factor₀))) ->
     ((BucketMapFraction.dividend max_load_factor₀) < (BucketMapFraction.divisor max_load_factor₀)) ->
      (capacity₀ ≥ 0) ->
       ((BucketMapFraction.divisor max_load_factor₀) ≠ 0) ->
        ((BucketMapFraction.dividend max_load_factor₀) ≠ 0) ->
         (k₀ ≥ 0) ->
          (((capacity₀ * (BucketMapFraction.dividend max_load_factor₀)) / (BucketMapFraction.divisor max_load_factor₀)) = (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) capacity₀)) * (BucketMapFraction.dividend max_load_factor₀)) / (BucketMapFraction.divisor max_load_factor₀))) ->
           (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) capacity₀)) * (BucketMapFraction.dividend max_load_factor₀)) ≥ (BucketMapFraction.divisor max_load_factor₀)) ->
            (0 = (bucket_map_total_len (t0 := Int) (bucket_map_empties (t0 := Int) capacity₀))) ->
             (bucket_map_keys_distributed_by_hash (t0 := Int) (bucket_map_empties (t0 := Int) capacity₀)) ->
              (bucket_map_unique_keys (t0 := Int) (bucket_map_empties (t0 := Int) capacity₀)) ->
               ((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) capacity₀)) > 0) ->
                (¬(alist_aseq_contains_key (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots (BucketMapHashMap.mkBucketMapHashMap₀ 0 max_load_factor₀ ((capacity₀ * (BucketMapFraction.dividend max_load_factor₀)) / (BucketMapFraction.divisor max_load_factor₀)) False (bucket_map_empties (t0 := Int) capacity₀))) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots (BucketMapHashMap.mkBucketMapHashMap₀ 0 max_load_factor₀ ((capacity₀ * (BucketMapFraction.dividend max_load_factor₀)) / (BucketMapFraction.divisor max_load_factor₀)) False (bucket_map_empties (t0 := Int) capacity₀)))))) k₀))
end F
