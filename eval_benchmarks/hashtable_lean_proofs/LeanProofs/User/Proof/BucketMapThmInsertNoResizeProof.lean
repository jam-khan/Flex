import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmInsertNoResize
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapThmInsertNoResizeQualifs

@[qualif]
def EqTrue (new_slf₀ : Prop) : Prop :=
  new_slf₀

@[qualif]
def EqFalse (new_slf₀ : Prop) : Prop :=
  (¬new_slf₀)

@[qualif]
def EqZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ = 0)

@[qualif]
def GtZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ > 0)

@[qualif]
def GeZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ ≥ 0)

@[qualif]
def LtZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ < 0)

@[qualif]
def LeZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ ≤ 0)

@[qualif]
def Eq (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ = a'₁)

@[qualif]
def Gt (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ > a'₁)

@[qualif]
def Ge (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ ≥ a'₁)

@[qualif]
def Lt (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ < a'₁)

@[qualif]
def Le (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ ≤ a'₁)

@[qualif]
def Le1 (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ ≤ (a'₁ - 1))

end BucketMapThmInsertNoResizeQualifs

open BucketMapThmInsertNoResizeQualifs

set_option maxHeartbeats 5000000
#time def BucketMapThmInsertNoResize_proof : BucketMapThmInsertNoResize := by
  unfold BucketMapThmInsertNoResize
  (try zap) ; (try simp [*]) ; (try solve)

end F
