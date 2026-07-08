import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__GetInList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0GetInListQualifs

@[qualif]
def EqTrue (ls₁ : Prop) : Prop :=
  ls₁

@[qualif]
def EqFalse (ls₁ : Prop) : Prop :=
  (¬ls₁)

@[qualif]
def EqZero (ls₁ : Int) : Prop :=
  (ls₁ = 0)

@[qualif]
def GtZero (ls₁ : Int) : Prop :=
  (ls₁ > 0)

@[qualif]
def GeZero (ls₁ : Int) : Prop :=
  (ls₁ ≥ 0)

@[qualif]
def LtZero (ls₁ : Int) : Prop :=
  (ls₁ < 0)

@[qualif]
def LeZero (ls₁ : Int) : Prop :=
  (ls₁ ≤ 0)

@[qualif]
def Eq (ls₁ : Int) (k₀ : Int) : Prop :=
  (ls₁ = k₀)

@[qualif]
def Gt (ls₁ : Int) (k₀ : Int) : Prop :=
  (ls₁ > k₀)

@[qualif]
def Ge (ls₁ : Int) (k₀ : Int) : Prop :=
  (ls₁ ≥ k₀)

@[qualif]
def Lt (ls₁ : Int) (k₀ : Int) : Prop :=
  (ls₁ < k₀)

@[qualif]
def Le (ls₁ : Int) (k₀ : Int) : Prop :=
  (ls₁ ≤ k₀)

@[qualif]
def Le1 (ls₁ : Int) (k₀ : Int) : Prop :=
  (ls₁ ≤ (k₀ - 1))

end BucketMapImpl0GetInListQualifs

open BucketMapImpl0GetInListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__GetInList_proof : BucketMapImpl__0__GetInList := by
  unfold BucketMapImpl__0__GetInList
  (try zap) ; (try simp [*]) ; (try solve)

end F
