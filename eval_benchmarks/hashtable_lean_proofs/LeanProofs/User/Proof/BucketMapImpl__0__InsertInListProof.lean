import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__InsertInList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0InsertInListQualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (new_slf₀ : Int) : Prop :=
  (a'₀ = new_slf₀)

@[qualif]
def Gt (a'₀ : Int) (new_slf₀ : Int) : Prop :=
  (a'₀ > new_slf₀)

@[qualif]
def Ge (a'₀ : Int) (new_slf₀ : Int) : Prop :=
  (a'₀ ≥ new_slf₀)

@[qualif]
def Lt (a'₀ : Int) (new_slf₀ : Int) : Prop :=
  (a'₀ < new_slf₀)

@[qualif]
def Le (a'₀ : Int) (new_slf₀ : Int) : Prop :=
  (a'₀ ≤ new_slf₀)

@[qualif]
def Le1 (a'₀ : Int) (new_slf₀ : Int) : Prop :=
  (a'₀ ≤ (new_slf₀ - 1))

end BucketMapImpl0InsertInListQualifs

open BucketMapImpl0InsertInListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__InsertInList_proof : BucketMapImpl__0__InsertInList := by
  unfold BucketMapImpl__0__InsertInList
  (try zap) ; (try simp [*]) ; (try solve)

end F
