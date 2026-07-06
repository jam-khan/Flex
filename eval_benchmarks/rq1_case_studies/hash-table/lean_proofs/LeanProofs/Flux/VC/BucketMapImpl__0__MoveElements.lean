import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.AlistAseqLen
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.SvecSet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
import LeanProofs.User.Fun.BucketMapAbsorbBucket
import LeanProofs.User.Fun.BucketMapAbsorbBuckets
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__MoveElements := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : (OVec (ASeq Int Int))) -> (a7 : (OVec (ASeq Int Int))) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Prop) -> (a13 : (OVec (ASeq Int Int))) -> (a14 : (OVec (ASeq Int Int))) -> Prop, ∃ k1 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : (OVec (ASeq Int Int))) -> (a8 : (OVec (ASeq Int Int))) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Prop) -> (a14 : (OVec (ASeq Int Int))) -> (a15 : (OVec (ASeq Int Int))) -> Prop, ∃ k2 : (a0 : (ASeq Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : (OVec (ASeq Int Int))) -> (a7 : (OVec (ASeq Int Int))) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Prop) -> (a14 : (OVec (ASeq Int Int))) -> (a15 : (OVec (ASeq Int Int))) -> Prop, 
 ∀ (t₀ : (BucketMapHashMap Int)),
  ∀ (s₀ : (OVec (ASeq Int Int))),
   ((BucketMapHashMap.max_load t₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)))) ->
    (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀))) ->
     ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀))) ->
      ((BucketMapHashMap.num_entries t₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots t₀))) ->
       (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots t₀)) ->
        (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots t₀)) ->
         ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots t₀)) > 0) ->
          (((k0 0 (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀))) ∧
          (∀ (a'₀ : (ASeq Int Int)),
           ((k1 a'₀ 0 (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀))) ∧
          (∀ (i₀ : Int),
           ∀ (a'₂ : (BucketMapHashMap Int)),
            ∀ (a'₃ : (OVec (ASeq Int Int))),
             ((k0 i₀ (BucketMapHashMap.num_entries a'₂) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₂)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₂)) (BucketMapHashMap.max_load a'₂) (BucketMapHashMap.saturated a'₂) (BucketMapHashMap.slots a'₂) a'₃ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀)) ->
              ((svec_len (t0 := (ASeq Int Int)) a'₃) ≥ 0) ->
               ((¬(i₀ < (svec_len (t0 := (ASeq Int Int)) a'₃))) ->
                (((BucketMapHashMap.max_load a'₂) = (BucketMapHashMap.max_load t₀))) ∧
                (((BucketMapHashMap.max_load_factor a'₂) = (BucketMapHashMap.max_load_factor t₀))) ∧
                (((BucketMapHashMap.saturated a'₂) = (BucketMapHashMap.saturated t₀))) ∧
                (((BucketMapHashMap.slots a'₂) = (bucket_map_absorb_buckets (t0 := Int) (BucketMapHashMap.slots t₀) s₀))) ∧
                ((a'₃ = (bucket_map_empties (t0 := Int) (svec_len (t0 := (ASeq Int Int)) s₀))))
                ) ∧
               ((i₀ < (svec_len (t0 := (ASeq Int Int)) a'₃)) ->
                (∀ (a'₄ : (ASeq Int Int)),
                 ((k1 a'₄ i₀ (BucketMapHashMap.num_entries a'₂) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₂)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₂)) (BucketMapHashMap.max_load a'₂) (BucketMapHashMap.saturated a'₂) (BucketMapHashMap.slots a'₂) a'₃ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀)) ->
                  ((k2 a'₄ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀ i₀ (BucketMapHashMap.num_entries a'₂) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₂)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₂)) (BucketMapHashMap.max_load a'₂) (BucketMapHashMap.saturated a'₂) (BucketMapHashMap.slots a'₂) a'₃))) ∧
                (((k2 (alist_aseq_nil (t0 := Int) (t1 := Int)) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀ i₀ (BucketMapHashMap.num_entries a'₂) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₂)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₂)) (BucketMapHashMap.max_load a'₂) (BucketMapHashMap.saturated a'₂) (BucketMapHashMap.slots a'₂) a'₃))) ∧
                (((k2 (svec_get (t0 := (ASeq Int Int)) a'₃ i₀) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀ i₀ (BucketMapHashMap.num_entries a'₂) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₂)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₂)) (BucketMapHashMap.max_load a'₂) (BucketMapHashMap.saturated a'₂) (BucketMapHashMap.slots a'₂) a'₃)) ->
                 ∀ (new_t₀ : (BucketMapHashMap Int)),
                  ((BucketMapHashMap.max_load new_t₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀)))) ->
                   (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀))) ->
                    ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀))) ->
                     ((BucketMapHashMap.num_entries new_t₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_t₀))) ->
                      (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_t₀)) ->
                       (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_t₀)) ->
                        ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_t₀)) > 0) ->
                         ((BucketMapHashMap.max_load new_t₀) = (BucketMapHashMap.max_load a'₂)) ->
                          ((BucketMapHashMap.max_load_factor new_t₀) = (BucketMapHashMap.max_load_factor a'₂)) ->
                           ((BucketMapHashMap.saturated new_t₀) = (BucketMapHashMap.saturated a'₂)) ->
                            ((BucketMapHashMap.num_entries new_t₀) ≥ (BucketMapHashMap.num_entries a'₂)) ->
                             ((BucketMapHashMap.num_entries new_t₀) ≤ ((BucketMapHashMap.num_entries a'₂) + (alist_aseq_len (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) a'₃ i₀)))) ->
                              ((BucketMapHashMap.slots new_t₀) = (bucket_map_absorb_bucket (t0 := Int) (BucketMapHashMap.slots a'₂) (svec_get (t0 := (ASeq Int Int)) a'₃ i₀))) ->
                               (((k0 (i₀ + 1) (BucketMapHashMap.num_entries new_t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀)) (BucketMapHashMap.max_load new_t₀) (BucketMapHashMap.saturated new_t₀) (BucketMapHashMap.slots new_t₀) (svec_set (t0 := (ASeq Int Int)) a'₃ i₀ (alist_aseq_nil (t0 := Int) (t1 := Int))) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀))) ∧
                               (∀ (a'₆ : (ASeq Int Int)),
                                ((k2 a'₆ (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀ i₀ (BucketMapHashMap.num_entries a'₂) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₂)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₂)) (BucketMapHashMap.max_load a'₂) (BucketMapHashMap.saturated a'₂) (BucketMapHashMap.slots a'₂) a'₃)) ->
                                 ((k1 a'₆ (i₀ + 1) (BucketMapHashMap.num_entries new_t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_t₀)) (BucketMapHashMap.max_load new_t₀) (BucketMapHashMap.saturated new_t₀) (BucketMapHashMap.slots new_t₀) (svec_set (t0 := (ASeq Int Int)) a'₃ i₀ (alist_aseq_nil (t0 := Int) (t1 := Int))) (BucketMapHashMap.num_entries t₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor t₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor t₀)) (BucketMapHashMap.max_load t₀) (BucketMapHashMap.saturated t₀) (BucketMapHashMap.slots t₀) s₀)))
                               )
                )
               )
          
end F
