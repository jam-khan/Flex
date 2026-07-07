import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferVecQueuePushCorrect
open Classical
set_option linter.unusedVariables false


namespace F

namespace RingbufferVecQueuePushCorrectQualifs

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
def Eq (a'₀ : Int) (b₀ : Int) : Prop :=
  (a'₀ = b₀)

@[qualif]
def Gt (a'₀ : Int) (b₀ : Int) : Prop :=
  (a'₀ > b₀)

@[qualif]
def Ge (a'₀ : Int) (b₀ : Int) : Prop :=
  (a'₀ ≥ b₀)

@[qualif]
def Lt (a'₀ : Int) (b₀ : Int) : Prop :=
  (a'₀ < b₀)

@[qualif]
def Le (a'₀ : Int) (b₀ : Int) : Prop :=
  (a'₀ ≤ b₀)

@[qualif]
def Le1 (a'₀ : Int) (b₀ : Int) : Prop :=
  (a'₀ ≤ (b₀ - 1))

end RingbufferVecQueuePushCorrectQualifs

open RingbufferVecQueuePushCorrectQualifs

set_option maxHeartbeats 5000000
#time def RingbufferVecQueuePushCorrect_proof : RingbufferVecQueuePushCorrect := by
  unfold RingbufferVecQueuePushCorrect
  solve_fixpoint_combo

end F
