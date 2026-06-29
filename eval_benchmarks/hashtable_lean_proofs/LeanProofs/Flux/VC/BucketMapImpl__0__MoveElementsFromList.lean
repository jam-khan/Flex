import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqLen
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.SvecSet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapAbsorbBucket
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__MoveElementsFromList := ∃ k0 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : (OVec (ASeq Int Int))) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Prop) -> (a12 : (OVec (ASeq Int Int))) -> (a13 : (ASeq Int Int)) -> Prop, 
 ∀ (t₀ : (BucketMapHashMap Int)),
  ∀ (ls₀ : (ASeq Int Int)),
   ((BucketMapHashMap.max_load t₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)))) ->
    (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀))) ->
     ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀))) ->
      ((BucketMapHashMap.num_entries t₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots t₀))) ->
       (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots t₀)) ->
        (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots t₀)) ->
         ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots t₀)) > 0) ->
          (((k0 ls₀ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) ls₀))) ∧
          (∀ (ls₁ : (ASeq Int Int)),
           ∀ (a'₁ : (BucketMapHashMap Int)),
            ((k0 ls₁ (BucketMapHashMap.num_entries a'₁) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₁)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₁)) (BucketMapHashMap.max_load a'₁) (BucketMapHashMap.saturated a'₁) (BucketMapHashMap.slots a'₁) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) ls₀)) ->
             (∀ (k₀ : Int),
              ∀ (t₁ : Int),
               ∀ (l₀ : (ASeq Int Int)),
                (ls₁ = (alist_aseq_cons (t0 := Int) (t1 := Int) k₀ t₁ l₀)) ->
                 (k₀ ≥ 0) ->
                  ∀ (new_slf₀ : (BucketMapHashMap Int)),
                   ((BucketMapHashMap.max_load new_slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)))) ->
                    (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
                     ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
                      ((BucketMapHashMap.num_entries new_slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_slf₀))) ->
                       (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                        (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                         ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) > 0) ->
                          ((BucketMapHashMap.max_load new_slf₀) = (BucketMapHashMap.max_load a'₁)) ->
                           ((BucketMapHashMap.max_load_factor new_slf₀) = (BucketMapHashMap.max_load_factor a'₁)) ->
                            ((BucketMapHashMap.saturated new_slf₀) = (BucketMapHashMap.saturated a'₁)) ->
                             ((BucketMapHashMap.num_entries new_slf₀) = ((BucketMapHashMap.num_entries a'₁) + (if (alist_aseq_contains_key (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots a'₁) (k₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots a'₁)))) k₀) then 0 else 1))) ->
                              ((BucketMapHashMap.slots new_slf₀) = (let a'₆ := (k₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots a'₁))); (let a'₇ := (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots a'₁) a'₆); (let a'₈ := (alist_aseq_contains_key (t0 := Int) (t1 := _) a'₇ k₀); (svec_set (t0 := (ASeq Int _)) (BucketMapHashMap.slots a'₁) a'₆ (if a'₈ then (alist_aseq_set (t0 := Int) (t1 := _) a'₇ k₀ t₁) else (alist_aseq_cons (t0 := Int) (t1 := _) k₀ t₁ a'₇))))))) ->
                               ((k0 l₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) ls₀))) ∧
             ((ls₁ = (alist_aseq_nil (t0 := Int) (t1 := Int))) ->
              (((BucketMapHashMap.max_load a'₁) = (BucketMapHashMap.max_load t₀))) ∧
              (((BucketMapHashMap.max_load_factor a'₁) = (BucketMapHashMap.max_load_factor t₀))) ∧
              (((BucketMapHashMap.saturated a'₁) = (BucketMapHashMap.saturated t₀))) ∧
              (((BucketMapHashMap.num_entries a'₁) ≥ (BucketMapHashMap.num_entries t₀))) ∧
              (((BucketMapHashMap.num_entries a'₁) ≤ ((BucketMapHashMap.num_entries t₀) + (alist_aseq_len (t0 := Int) (t1 := Int) ls₀)))) ∧
              (((BucketMapHashMap.slots a'₁) = (bucket_map_absorb_bucket (t0 := Int) (BucketMapHashMap.slots t₀) ls₀)))
              )
             )
          
end F
