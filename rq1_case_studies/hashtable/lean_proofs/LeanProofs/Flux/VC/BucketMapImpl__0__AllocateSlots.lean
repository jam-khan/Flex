import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Struct.OVec
import LeanProofs.User.Fun.AlistAseqNil
import LeanProofs.User.Fun.SvecEmpty
import LeanProofs.User.Fun.SvecPush
import LeanProofs.User.Fun.BucketMapEmpties
open Classical
set_option linter.unusedVariables false


namespace F



def BucketMapImpl__0__AllocateSlots := ∃ k0 : (a0 : (OVec (ASeq Int Int))) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 (svec_empty (t0 := (ASeq Int Int))) n₀ n₀))) ∧
   (∀ (slots₀ : (OVec (ASeq Int Int))),
    ∀ (n₁ : Int),
     ((k0 slots₀ n₁ n₀)) ->
      ((¬(n₁ > 0)) ->
       (slots₀ = (bucket_map_empties (t0 := Int) n₀))) ∧
      ((n₁ > 0) ->
       (((n₁ - 1) ≥ 0)) ∧
       (((k0 (svec_push (t0 := (ASeq Int Int)) slots₀ (alist_aseq_nil (t0 := Int) (t1 := Int))) (n₁ - 1) n₀)))
       )
      )
   
end F
