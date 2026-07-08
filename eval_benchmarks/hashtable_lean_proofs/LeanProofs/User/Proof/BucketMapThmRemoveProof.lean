import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmRemove
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapThmRemoveQualifs

@[qualif]
def EqTrue (is_some₀ : Prop) : Prop :=
  is_some₀

@[qualif]
def EqFalse (is_some₀ : Prop) : Prop :=
  (¬is_some₀)

@[qualif]
def EqZero (is_some₀ : Int) : Prop :=
  (is_some₀ = 0)

@[qualif]
def GtZero (is_some₀ : Int) : Prop :=
  (is_some₀ > 0)

@[qualif]
def GeZero (is_some₀ : Int) : Prop :=
  (is_some₀ ≥ 0)

@[qualif]
def LtZero (is_some₀ : Int) : Prop :=
  (is_some₀ < 0)

@[qualif]
def LeZero (is_some₀ : Int) : Prop :=
  (is_some₀ ≤ 0)

@[qualif]
def Eq (is_some₀ : Int) (new_slf₀ : Int) : Prop :=
  (is_some₀ = new_slf₀)

@[qualif]
def Gt (is_some₀ : Int) (new_slf₀ : Int) : Prop :=
  (is_some₀ > new_slf₀)

@[qualif]
def Ge (is_some₀ : Int) (new_slf₀ : Int) : Prop :=
  (is_some₀ ≥ new_slf₀)

@[qualif]
def Lt (is_some₀ : Int) (new_slf₀ : Int) : Prop :=
  (is_some₀ < new_slf₀)

@[qualif]
def Le (is_some₀ : Int) (new_slf₀ : Int) : Prop :=
  (is_some₀ ≤ new_slf₀)

@[qualif]
def Le1 (is_some₀ : Int) (new_slf₀ : Int) : Prop :=
  (is_some₀ ≤ (new_slf₀ - 1))

end BucketMapThmRemoveQualifs

open BucketMapThmRemoveQualifs

set_option maxHeartbeats 5000000
#time def BucketMapThmRemove_proof : BucketMapThmRemove := by
  unfold BucketMapThmRemove
  (try zap) ; (try simp [*]) ; (try solve)

end F
