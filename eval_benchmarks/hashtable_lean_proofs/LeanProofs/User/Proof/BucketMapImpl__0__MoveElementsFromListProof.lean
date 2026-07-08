import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__MoveElementsFromList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0MoveElementsFromListQualifs

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
def Eq (ls₁ : Int) (a'₁ : Int) : Prop :=
  (ls₁ = a'₁)

@[qualif]
def Gt (ls₁ : Int) (a'₁ : Int) : Prop :=
  (ls₁ > a'₁)

@[qualif]
def Ge (ls₁ : Int) (a'₁ : Int) : Prop :=
  (ls₁ ≥ a'₁)

@[qualif]
def Lt (ls₁ : Int) (a'₁ : Int) : Prop :=
  (ls₁ < a'₁)

@[qualif]
def Le (ls₁ : Int) (a'₁ : Int) : Prop :=
  (ls₁ ≤ a'₁)

@[qualif]
def Le1 (ls₁ : Int) (a'₁ : Int) : Prop :=
  (ls₁ ≤ (a'₁ - 1))

end BucketMapImpl0MoveElementsFromListQualifs

open BucketMapImpl0MoveElementsFromListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__MoveElementsFromList_proof : BucketMapImpl__0__MoveElementsFromList := by
  unfold BucketMapImpl__0__MoveElementsFromList
  (try zap) ; (try simp [*]) ; (try solve)

end F
