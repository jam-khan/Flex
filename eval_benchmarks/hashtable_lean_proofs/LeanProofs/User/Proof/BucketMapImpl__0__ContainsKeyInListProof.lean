import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__ContainsKeyInList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0ContainsKeyInListQualifs

@[qualif]
def EqTrue (ls₀ : Prop) : Prop :=
  ls₀

@[qualif]
def EqFalse (ls₀ : Prop) : Prop :=
  (¬ls₀)

@[qualif]
def EqZero (ls₀ : Int) : Prop :=
  (ls₀ = 0)

@[qualif]
def GtZero (ls₀ : Int) : Prop :=
  (ls₀ > 0)

@[qualif]
def GeZero (ls₀ : Int) : Prop :=
  (ls₀ ≥ 0)

@[qualif]
def LtZero (ls₀ : Int) : Prop :=
  (ls₀ < 0)

@[qualif]
def LeZero (ls₀ : Int) : Prop :=
  (ls₀ ≤ 0)

@[qualif]
def Eq (ls₀ : Int) (k₁ : Int) : Prop :=
  (ls₀ = k₁)

@[qualif]
def Gt (ls₀ : Int) (k₁ : Int) : Prop :=
  (ls₀ > k₁)

@[qualif]
def Ge (ls₀ : Int) (k₁ : Int) : Prop :=
  (ls₀ ≥ k₁)

@[qualif]
def Lt (ls₀ : Int) (k₁ : Int) : Prop :=
  (ls₀ < k₁)

@[qualif]
def Le (ls₀ : Int) (k₁ : Int) : Prop :=
  (ls₀ ≤ k₁)

@[qualif]
def Le1 (ls₀ : Int) (k₁ : Int) : Prop :=
  (ls₀ ≤ (k₁ - 1))

end BucketMapImpl0ContainsKeyInListQualifs

open BucketMapImpl0ContainsKeyInListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__ContainsKeyInList_proof : BucketMapImpl__0__ContainsKeyInList := by
  unfold BucketMapImpl__0__ContainsKeyInList
  (try zap) ; (try simp [*]) ; (try solve)

end F
