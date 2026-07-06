import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmNew
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapThmNewQualifs

@[qualif]
def EqTrue (res₀ : Prop) : Prop :=
  res₀

@[qualif]
def EqFalse (res₀ : Prop) : Prop :=
  (¬res₀)

@[qualif]
def EqZero (res₀ : Int) : Prop :=
  (res₀ = 0)

@[qualif]
def GtZero (res₀ : Int) : Prop :=
  (res₀ > 0)

@[qualif]
def GeZero (res₀ : Int) : Prop :=
  (res₀ ≥ 0)

@[qualif]
def LtZero (res₀ : Int) : Prop :=
  (res₀ < 0)

@[qualif]
def LeZero (res₀ : Int) : Prop :=
  (res₀ ≤ 0)

@[qualif]
def Eq (res₀ : Int) (a'₁ : Int) : Prop :=
  (res₀ = a'₁)

@[qualif]
def Gt (res₀ : Int) (a'₁ : Int) : Prop :=
  (res₀ > a'₁)

@[qualif]
def Ge (res₀ : Int) (a'₁ : Int) : Prop :=
  (res₀ ≥ a'₁)

@[qualif]
def Lt (res₀ : Int) (a'₁ : Int) : Prop :=
  (res₀ < a'₁)

@[qualif]
def Le (res₀ : Int) (a'₁ : Int) : Prop :=
  (res₀ ≤ a'₁)

@[qualif]
def Le1 (res₀ : Int) (a'₁ : Int) : Prop :=
  (res₀ ≤ (a'₁ - 1))

end BucketMapThmNewQualifs

open BucketMapThmNewQualifs

set_option maxHeartbeats 5000000
#time def BucketMapThmNew_proof : BucketMapThmNew := by
  unfold BucketMapThmNew
  solve_fixpoint_combo

end F
