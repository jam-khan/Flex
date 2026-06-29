import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmRemoveFromList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapThmRemoveFromListQualifs

@[qualif]
def EqTrue (ls_res₀ : Prop) : Prop :=
  ls_res₀

@[qualif]
def EqFalse (ls_res₀ : Prop) : Prop :=
  (¬ls_res₀)

@[qualif]
def EqZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ = 0)

@[qualif]
def GtZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ > 0)

@[qualif]
def GeZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ ≥ 0)

@[qualif]
def LtZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ < 0)

@[qualif]
def LeZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ ≤ 0)

@[qualif]
def Eq (ls_res₀ : Int) (is_some₀ : Int) : Prop :=
  (ls_res₀ = is_some₀)

@[qualif]
def Gt (ls_res₀ : Int) (is_some₀ : Int) : Prop :=
  (ls_res₀ > is_some₀)

@[qualif]
def Ge (ls_res₀ : Int) (is_some₀ : Int) : Prop :=
  (ls_res₀ ≥ is_some₀)

@[qualif]
def Lt (ls_res₀ : Int) (is_some₀ : Int) : Prop :=
  (ls_res₀ < is_some₀)

@[qualif]
def Le (ls_res₀ : Int) (is_some₀ : Int) : Prop :=
  (ls_res₀ ≤ is_some₀)

@[qualif]
def Le1 (ls_res₀ : Int) (is_some₀ : Int) : Prop :=
  (ls_res₀ ≤ (is_some₀ - 1))

end BucketMapThmRemoveFromListQualifs

open BucketMapThmRemoveFromListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapThmRemoveFromList_proof : BucketMapThmRemoveFromList := by
  unfold BucketMapThmRemoveFromList
  solve_fixpoint_combo

end F
