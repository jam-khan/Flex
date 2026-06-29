import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__RemoveFromList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0RemoveFromListQualifs

@[qualif]
def EqTrue (k₁ : Prop) : Prop :=
  k₁

@[qualif]
def EqFalse (k₁ : Prop) : Prop :=
  (¬k₁)

@[qualif]
def EqZero (k₁ : Int) : Prop :=
  (k₁ = 0)

@[qualif]
def GtZero (k₁ : Int) : Prop :=
  (k₁ > 0)

@[qualif]
def GeZero (k₁ : Int) : Prop :=
  (k₁ ≥ 0)

@[qualif]
def LtZero (k₁ : Int) : Prop :=
  (k₁ < 0)

@[qualif]
def LeZero (k₁ : Int) : Prop :=
  (k₁ ≤ 0)

@[qualif]
def Eq (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ = t₀)

@[qualif]
def Gt (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ > t₀)

@[qualif]
def Ge (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ ≥ t₀)

@[qualif]
def Lt (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ < t₀)

@[qualif]
def Le (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ ≤ t₀)

@[qualif]
def Le1 (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ ≤ (t₀ - 1))

end BucketMapImpl0RemoveFromListQualifs

open BucketMapImpl0RemoveFromListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__RemoveFromList_proof : BucketMapImpl__0__RemoveFromList := by
  unfold BucketMapImpl__0__RemoveFromList
  solve_fixpoint_combo

end F
