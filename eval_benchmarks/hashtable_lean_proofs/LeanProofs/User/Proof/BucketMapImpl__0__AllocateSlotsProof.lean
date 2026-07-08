import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__AllocateSlots
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0AllocateSlotsQualifs

@[qualif]
def EqTrue (slots₀ : Prop) : Prop :=
  slots₀

@[qualif]
def EqFalse (slots₀ : Prop) : Prop :=
  (¬slots₀)

@[qualif]
def EqZero (slots₀ : Int) : Prop :=
  (slots₀ = 0)

@[qualif]
def GtZero (slots₀ : Int) : Prop :=
  (slots₀ > 0)

@[qualif]
def GeZero (slots₀ : Int) : Prop :=
  (slots₀ ≥ 0)

@[qualif]
def LtZero (slots₀ : Int) : Prop :=
  (slots₀ < 0)

@[qualif]
def LeZero (slots₀ : Int) : Prop :=
  (slots₀ ≤ 0)

@[qualif]
def Eq (slots₀ : Int) (n₁ : Int) : Prop :=
  (slots₀ = n₁)

@[qualif]
def Gt (slots₀ : Int) (n₁ : Int) : Prop :=
  (slots₀ > n₁)

@[qualif]
def Ge (slots₀ : Int) (n₁ : Int) : Prop :=
  (slots₀ ≥ n₁)

@[qualif]
def Lt (slots₀ : Int) (n₁ : Int) : Prop :=
  (slots₀ < n₁)

@[qualif]
def Le (slots₀ : Int) (n₁ : Int) : Prop :=
  (slots₀ ≤ n₁)

@[qualif]
def Le1 (slots₀ : Int) (n₁ : Int) : Prop :=
  (slots₀ ≤ (n₁ - 1))

end BucketMapImpl0AllocateSlotsQualifs

open BucketMapImpl0AllocateSlotsQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__AllocateSlots_proof : BucketMapImpl__0__AllocateSlots := by
  unfold BucketMapImpl__0__AllocateSlots
  (try zap) ; (try simp [*]) ; (try solve)

end F
