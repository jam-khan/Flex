import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmMoveElementsFromList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapThmMoveElementsFromListQualifs

@[qualif]
def EqTrue (new_t₀ : Prop) : Prop :=
  new_t₀

@[qualif]
def EqFalse (new_t₀ : Prop) : Prop :=
  (¬new_t₀)

@[qualif]
def EqZero (new_t₀ : Int) : Prop :=
  (new_t₀ = 0)

@[qualif]
def GtZero (new_t₀ : Int) : Prop :=
  (new_t₀ > 0)

@[qualif]
def GeZero (new_t₀ : Int) : Prop :=
  (new_t₀ ≥ 0)

@[qualif]
def LtZero (new_t₀ : Int) : Prop :=
  (new_t₀ < 0)

@[qualif]
def LeZero (new_t₀ : Int) : Prop :=
  (new_t₀ ≤ 0)

@[qualif]
def Eq (new_t₀ : Int) (a'₁ : Int) : Prop :=
  (new_t₀ = a'₁)

@[qualif]
def Gt (new_t₀ : Int) (a'₁ : Int) : Prop :=
  (new_t₀ > a'₁)

@[qualif]
def Ge (new_t₀ : Int) (a'₁ : Int) : Prop :=
  (new_t₀ ≥ a'₁)

@[qualif]
def Lt (new_t₀ : Int) (a'₁ : Int) : Prop :=
  (new_t₀ < a'₁)

@[qualif]
def Le (new_t₀ : Int) (a'₁ : Int) : Prop :=
  (new_t₀ ≤ a'₁)

@[qualif]
def Le1 (new_t₀ : Int) (a'₁ : Int) : Prop :=
  (new_t₀ ≤ (a'₁ - 1))

end BucketMapThmMoveElementsFromListQualifs

open BucketMapThmMoveElementsFromListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapThmMoveElementsFromList_proof : BucketMapThmMoveElementsFromList := by
  unfold BucketMapThmMoveElementsFromList
  (try zap) ; (try simp [*]) ; (try solve)

end F
