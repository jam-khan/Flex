import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
import LeanProofs.User.Fun.BucketMapAbsorbBuckets
import LeanProofs.Flux.Fun.NumImpl11MAX
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__TryResize := 
 ∀ (slf₀ : (BucketMapHashMap Int)),
  ((BucketMapHashMap.max_load slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ->
   (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
    ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
     ((BucketMapHashMap.num_entries slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots slf₀))) ->
      (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots slf₀)) ->
       (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots slf₀)) ->
        ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) > 0) ->
         ((BucketMapHashMap.num_entries slf₀) ≥ 0) ->
          ((BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) ≠ 0) ->
           ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) ≠ 0) ->
            ((BucketMapHashMap.max_load slf₀) ≥ 0) ->
             ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≥ 0) ->
              ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) ≥ 0) ->
               ((BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) ≥ 0) ->
                (((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) ≠ 0)) ∧
                (((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) ≠ 0) ->
                 ((¬((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≤ ((18446744073709551615 / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))))) ->
                  ((((BucketMapHashMap.num_entries slf₀) = (BucketMapHashMap.num_entries slf₀))) ∧
                  (((BucketMapFraction.mkBucketMapFraction₀ (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) = (BucketMapHashMap.max_load_factor slf₀)))
                  ) ∧
                  (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≤ ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)))) ->
                   ((BucketMapHashMap.slots slf₀) = (bucket_map_absorb_buckets (t0 := Int) (bucket_map_empties (t0 := Int) (2 * (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) (BucketMapHashMap.slots slf₀)))) ∧
                  (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) > ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)))) ->
                   (((BucketMapHashMap.max_load slf₀) = (BucketMapHashMap.max_load slf₀))) ∧
                   (((BucketMapHashMap.slots slf₀) = (BucketMapHashMap.slots slf₀)))
                   )
                  ) ∧
                 (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≤ ((18446744073709551615 / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)))) ->
                  (((((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2) > 0)) ∧
                  (((((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))))
                  ) ∧
                  ((((((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) = (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2))) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ->
                   (((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2))) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
                    (0 = (bucket_map_total_len (t0 := Int) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2)))) ->
                     (bucket_map_keys_distributed_by_hash (t0 := Int) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2))) ->
                      (bucket_map_unique_keys (t0 := Int) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2))) ->
                       ((svec_len (t0 := (ASeq Int Int)) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2))) > 0) ->
                        ∀ (new_t₀ : (BucketMapHashMap Int)),
                         ((BucketMapHashMap.max_load new_t₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀)))) ->
                          (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀))) ->
                           ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀))) ->
                            ((BucketMapHashMap.num_entries new_t₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_t₀))) ->
                             (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_t₀)) ->
                              (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_t₀)) ->
                               ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) > 0) ->
                                ((BucketMapHashMap.max_load new_t₀) = ((((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ->
                                 ((BucketMapHashMap.max_load_factor new_t₀) = (BucketMapFraction.mkBucketMapFraction₀ (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ->
                                  ((BucketMapHashMap.saturated new_t₀) = False) ->
                                   ((BucketMapHashMap.slots new_t₀) = (bucket_map_absorb_buckets (t0 := Int) (bucket_map_empties (t0 := Int) ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * 2)) (BucketMapHashMap.slots slf₀))) ->
                                    ((BucketMapHashMap.num_entries new_t₀) ≥ 0) ->
                                     ((BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀)) ≠ 0) ->
                                      ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀)) ≠ 0) ->
                                       ((BucketMapHashMap.max_load new_t₀) ≥ 0) ->
                                        (((BucketMapHashMap.max_load new_t₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))))) ∧
                                        ((((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ∧
                                        (((BucketMapHashMap.num_entries slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_t₀)))) ∧
                                        ((((BucketMapHashMap.num_entries slf₀) = (BucketMapHashMap.num_entries slf₀))) ∧
                                        (((BucketMapFraction.mkBucketMapFraction₀ (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) = (BucketMapHashMap.max_load_factor slf₀)))
                                        ) ∧
                                        (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) ≤ ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)))) ->
                                         ((BucketMapHashMap.slots new_t₀) = (bucket_map_absorb_buckets (t0 := Int) (bucket_map_empties (t0 := Int) (2 * (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) (BucketMapHashMap.slots slf₀)))) ∧
                                        (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) > ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)))) ->
                                         (((BucketMapHashMap.max_load new_t₀) = (BucketMapHashMap.max_load slf₀))) ∧
                                         (((BucketMapHashMap.slots new_t₀) = (BucketMapHashMap.slots slf₀))) ∧
                                         (((BucketMapHashMap.saturated slf₀) = True))
                                         )
                                        )
                  )
                 )
                
end F
