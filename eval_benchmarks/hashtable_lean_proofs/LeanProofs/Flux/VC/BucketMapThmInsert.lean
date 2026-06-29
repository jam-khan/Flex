import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqKeyMatches
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.SvecSet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
import LeanProofs.User.Fun.BucketMapAbsorbBuckets
import LeanProofs.Flux.Fun.NumImpl11MAX
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapThmInsert := 
 ∀ (hm₀ : (BucketMapHashMap Int)),
  ∀ (k₀ : Int),
   ∀ (v₀ : Int),
    ∀ (k2₀ : Int),
     ∀ (v2₀ : Int),
      (k2₀ ≠ k₀) ->
       ((BucketMapHashMap.max_load hm₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀)))) ->
        (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀))) ->
         ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor hm₀))) ->
          ((BucketMapHashMap.num_entries hm₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots hm₀))) ->
           (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots hm₀)) ->
            (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots hm₀)) ->
             ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots hm₀)) > 0) ->
              (k₀ ≥ 0) ->
               (k2₀ ≥ 0) ->
                ∀ (new_slf₀ : (BucketMapHashMap Int)),
                 ((BucketMapHashMap.max_load new_slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)))) ->
                  (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
                   ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
                    ((BucketMapHashMap.num_entries new_slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_slf₀))) ->
                     (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                      (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                       ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) > 0) ->
                        ((BucketMapHashMap.max_load_factor new_slf₀) = (BucketMapHashMap.max_load_factor hm₀)) ->
                         ((BucketMapHashMap.slots new_slf₀) = (let a'₄ := (let a'₁ := (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀))); (let a'₂ := (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) a'₁); (let a'₃ := (alist_aseq_contains_key (t0 := Int) (t1 := _) a'₂ k₀); (svec_set (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) a'₁ (if a'₃ then (alist_aseq_set (t0 := Int) (t1 := _) a'₂ k₀ v₀) else (alist_aseq_cons (t0 := Int) (t1 := _) k₀ v₀ a'₂)))))); (if ((((bucket_map_total_len (t0 := _) a'₄) > (BucketMapHashMap.max_load hm₀)) ∧ (¬(BucketMapHashMap.saturated hm₀))) ∧ ((svec_len (t0 := (ASeq Int _)) a'₄) ≤ ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor hm₀))))) then (bucket_map_absorb_buckets (t0 := _) (bucket_map_empties (t0 := _) (2 * (svec_len (t0 := (ASeq Int _)) a'₄))) a'₄) else a'₄))) ->
                          ((alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_slf₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_slf₀)))) k₀ v₀)) ∧
                          (((alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) (k2₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀)))) k2₀ v2₀) <-> (alist_aseq_key_matches (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_slf₀) (k2₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots new_slf₀)))) k2₀ v2₀))) ∧
                          (((BucketMapHashMap.num_entries new_slf₀) = ((BucketMapHashMap.num_entries hm₀) + (if (alist_aseq_contains_key (t0 := Int) (t1 := _) (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀) (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots hm₀)))) k₀) then 0 else 1))))
                          
end F
