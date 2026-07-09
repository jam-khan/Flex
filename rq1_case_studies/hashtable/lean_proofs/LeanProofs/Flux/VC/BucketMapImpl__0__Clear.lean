import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.SvecSet
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__Clear := ∃ k0 : (a0 : Int) -> (a1 : (OVec (ASeq Int Int))) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : (OVec (ASeq Int Int))) -> Prop, 
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
             (((k0 0 (BucketMapHashMap.slots slf₀) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀)))) ∧
             (∀ (i₀ : Int),
              ∀ (a'₁ : (OVec (ASeq Int Int))),
               ((k0 i₀ a'₁ (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀))) ->
                ((svec_len (t0 := (ASeq Int Int)) a'₁) ≥ 0) ->
                 ((¬(i₀ < (svec_len (t0 := (ASeq Int Int)) a'₁))) ->
                  (((BucketMapHashMap.max_load slf₀) = (((svec_len (t0 := (ASeq Int Int)) a'₁) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))))) ∧
                  ((((svec_len (t0 := (ASeq Int Int)) a'₁) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ∧
                  ((0 = (bucket_map_total_len (t0 := Int) a'₁))) ∧
                  ((bucket_map_keys_distributed_by_hash (t0 := Int) a'₁)) ∧
                  ((bucket_map_unique_keys (t0 := Int) a'₁)) ∧
                  (((svec_len (t0 := (ASeq Int Int)) a'₁) > 0)) ∧
                  ((a'₁ = (bucket_map_empties (t0 := Int) (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))))
                  ) ∧
                 ((i₀ < (svec_len (t0 := (ASeq Int Int)) a'₁)) ->
                  ((k0 (i₀ + 1) (svec_set (t0 := (ASeq Int Int)) a'₁ i₀ (alist_aseq_nil (t0 := Int) (t1 := Int))) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀))))
                 )
             
end F
