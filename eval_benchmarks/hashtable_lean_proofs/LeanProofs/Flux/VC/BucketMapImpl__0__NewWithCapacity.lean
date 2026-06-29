import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__NewWithCapacity := 
 ∀ (capacity₀ : Int),
  ∀ (max_load_factor₀ : BucketMapFraction),
   ((capacity₀ > 0) ∧ ((capacity₀ * (BucketMapFraction.dividend max_load_factor₀)) ≥ (BucketMapFraction.divisor max_load_factor₀))) ->
    ((BucketMapFraction.dividend max_load_factor₀) < (BucketMapFraction.divisor max_load_factor₀)) ->
     (capacity₀ ≥ 0) ->
      ((BucketMapFraction.divisor max_load_factor₀) ≠ 0) ->
       ((BucketMapFraction.dividend max_load_factor₀) ≠ 0) ->
        ((BucketMapFraction.dividend max_load_factor₀) ≥ 0) ->
         ((BucketMapFraction.divisor max_load_factor₀) ≥ 0) ->
          (((BucketMapFraction.divisor max_load_factor₀) ≠ 0)) ∧
          (((BucketMapFraction.divisor max_load_factor₀) ≠ 0) ->
           ((((capacity₀ * (BucketMapFraction.dividend max_load_factor₀)) / (BucketMapFraction.divisor max_load_factor₀)) = (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) capacity₀)) * (BucketMapFraction.dividend max_load_factor₀)) / (BucketMapFraction.divisor max_load_factor₀)))) ∧
           ((((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) capacity₀)) * (BucketMapFraction.dividend max_load_factor₀)) ≥ (BucketMapFraction.divisor max_load_factor₀))) ∧
           ((0 = (bucket_map_total_len (t0 := Int) (bucket_map_empties (t0 := Int) capacity₀)))) ∧
           ((bucket_map_keys_distributed_by_hash (t0 := Int) (bucket_map_empties (t0 := Int) capacity₀))) ∧
           ((bucket_map_unique_keys (t0 := Int) (bucket_map_empties (t0 := Int) capacity₀))) ∧
           (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) capacity₀)) > 0))
           )
          
end F
