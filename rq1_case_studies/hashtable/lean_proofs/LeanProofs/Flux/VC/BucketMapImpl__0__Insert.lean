import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.Flux.Struct.BucketMapHashMap
import LeanProofs.Flux.Struct.BucketMapFraction
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqContainsKey
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



def BucketMapImpl__0__Insert := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : (OVec (ASeq Int Int))) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Prop) -> (a13 : (OVec (ASeq Int Int))) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : (OVec (ASeq Int Int))) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Prop) -> (a11 : (OVec (ASeq Int Int))) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Prop) -> (a19 : (OVec (ASeq Int Int))) -> Prop, 
 ∀ (slf₀ : (BucketMapHashMap Int)),
  ∀ (key₀ : Int),
   ∀ (val₀ : Int),
    ((BucketMapHashMap.max_load slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)))) ->
     (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
      ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀))) ->
       ((BucketMapHashMap.num_entries slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots slf₀))) ->
        (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots slf₀)) ->
         (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots slf₀)) ->
          ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)) > 0) ->
           (key₀ ≥ 0) ->
            ∀ (new_slf₀ : (BucketMapHashMap Int)),
             ((BucketMapHashMap.max_load new_slf₀) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)))) ->
              (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
               ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀))) ->
                ((BucketMapHashMap.num_entries new_slf₀) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_slf₀))) ->
                 (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                  (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_slf₀)) ->
                   ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) > 0) ->
                    ((BucketMapHashMap.max_load new_slf₀) = (BucketMapHashMap.max_load slf₀)) ->
                     ((BucketMapHashMap.max_load_factor new_slf₀) = (BucketMapHashMap.max_load_factor slf₀)) ->
                      ((BucketMapHashMap.saturated new_slf₀) = (BucketMapHashMap.saturated slf₀)) ->
                       ((BucketMapHashMap.num_entries new_slf₀) = ((BucketMapHashMap.num_entries slf₀) + (if (alist_aseq_contains_key (t0 := Int) (t1 := Int) (svec_get (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀) (key₀ % (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots slf₀)))) key₀) then 0 else 1))) ->
                        ((BucketMapHashMap.slots new_slf₀) = (let a'₁ := (key₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀))); (let a'₂ := (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀) a'₁); (let a'₃ := (alist_aseq_contains_key (t0 := Int) (t1 := _) a'₂ key₀); (svec_set (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀) a'₁ (if a'₃ then (alist_aseq_set (t0 := Int) (t1 := _) a'₂ key₀ val₀) else (alist_aseq_cons (t0 := Int) (t1 := _) key₀ val₀ a'₂))))))) ->
                         ((BucketMapHashMap.num_entries new_slf₀) ≥ 0) ->
                          ((BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) ≠ 0) ->
                           ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) ≠ 0) ->
                            ((BucketMapHashMap.max_load new_slf₀) ≥ 0) ->
                             ((¬((BucketMapHashMap.num_entries new_slf₀) > (BucketMapHashMap.max_load new_slf₀))) ->
                              ((k0 (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ val₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀)))) ∧
                             (((BucketMapHashMap.num_entries new_slf₀) > (BucketMapHashMap.max_load new_slf₀)) ->
                              ((¬(BucketMapHashMap.saturated new_slf₀)) ->
                               ∀ (new_slf₁ : (BucketMapHashMap Int)),
                                ((BucketMapHashMap.max_load new_slf₁) = (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₁)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₁))) / (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₁)))) ->
                                 (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₁)) * (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₁))) ≥ (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₁))) ->
                                  ((BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₁)) < (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₁))) ->
                                   ((BucketMapHashMap.num_entries new_slf₁) = (bucket_map_total_len (t0 := Int) (BucketMapHashMap.slots new_slf₁))) ->
                                    (bucket_map_keys_distributed_by_hash (t0 := Int) (BucketMapHashMap.slots new_slf₁)) ->
                                     (bucket_map_unique_keys (t0 := Int) (BucketMapHashMap.slots new_slf₁)) ->
                                      ((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₁)) > 0) ->
                                       (((BucketMapHashMap.num_entries new_slf₁) = (BucketMapHashMap.num_entries new_slf₀)) ∧ ((BucketMapHashMap.max_load_factor new_slf₁) = (BucketMapHashMap.max_load_factor new_slf₀))) ->
                                        (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) ≤ ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)))) -> ((BucketMapHashMap.slots new_slf₁) = (bucket_map_absorb_buckets (t0 := Int) (bucket_map_empties (t0 := Int) (2 * (svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)))) (BucketMapHashMap.slots new_slf₀)))) ->
                                         (((svec_len (t0 := (ASeq Int Int)) (BucketMapHashMap.slots new_slf₀)) > ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)))) -> ((((BucketMapHashMap.max_load new_slf₁) = (BucketMapHashMap.max_load new_slf₀)) ∧ ((BucketMapHashMap.slots new_slf₁) = (BucketMapHashMap.slots new_slf₀))) ∧ ((BucketMapHashMap.saturated new_slf₁) = True))) ->
                                          ((k1 (BucketMapHashMap.num_entries new_slf₁) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₁)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₁)) (BucketMapHashMap.max_load new_slf₁) (BucketMapHashMap.saturated new_slf₁) (BucketMapHashMap.slots new_slf₁) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ val₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀)))) ∧
                              ((BucketMapHashMap.saturated new_slf₀) ->
                               ((k0 (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ val₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) True (BucketMapHashMap.slots new_slf₀))))
                              ) ∧
                             (((k0 (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ val₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀))) ->
                              ((k1 (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ val₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀)))) ∧
                             (∀ (a'₅ : (BucketMapHashMap Int)),
                              ((k1 (BucketMapHashMap.num_entries a'₅) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor a'₅)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor a'₅)) (BucketMapHashMap.max_load a'₅) (BucketMapHashMap.saturated a'₅) (BucketMapHashMap.slots a'₅) (BucketMapHashMap.num_entries slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor slf₀)) (BucketMapHashMap.max_load slf₀) (BucketMapHashMap.saturated slf₀) (BucketMapHashMap.slots slf₀) key₀ val₀ (BucketMapHashMap.num_entries new_slf₀) (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapFraction.divisor (BucketMapHashMap.max_load_factor new_slf₀)) (BucketMapHashMap.max_load new_slf₀) (BucketMapHashMap.saturated new_slf₀) (BucketMapHashMap.slots new_slf₀))) ->
                               (((BucketMapHashMap.max_load_factor a'₅) = (BucketMapHashMap.max_load_factor slf₀))) ∧
                               (((BucketMapHashMap.slots a'₅) = (let a'₉ := (let a'₆ := (key₀ % (svec_len (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀))); (let a'₇ := (svec_get (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀) a'₆); (let a'₈ := (alist_aseq_contains_key (t0 := Int) (t1 := _) a'₇ key₀); (svec_set (t0 := (ASeq Int _)) (BucketMapHashMap.slots slf₀) a'₆ (if a'₈ then (alist_aseq_set (t0 := Int) (t1 := _) a'₇ key₀ val₀) else (alist_aseq_cons (t0 := Int) (t1 := _) key₀ val₀ a'₇)))))); (if ((((bucket_map_total_len (t0 := _) a'₉) > (BucketMapHashMap.max_load slf₀)) ∧ (¬(BucketMapHashMap.saturated slf₀))) ∧ ((svec_len (t0 := (ASeq Int _)) a'₉) ≤ ((num_impl_11_MAX / 2) / (BucketMapFraction.dividend (BucketMapHashMap.max_load_factor slf₀))))) then (bucket_map_absorb_buckets (t0 := _) (bucket_map_empties (t0 := _) (2 * (svec_len (t0 := (ASeq Int _)) a'₉))) a'₉) else a'₉))))
                               )
                             
end F
