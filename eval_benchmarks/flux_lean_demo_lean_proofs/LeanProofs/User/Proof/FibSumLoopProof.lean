import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibSumLoop
open Classical
set_option linter.unusedVariables false


namespace F

namespace FibSumLoopQualifs

@[qualif]
def EqTrue (total₀ : Prop) : Prop :=
  total₀

@[qualif]
def EqFalse (total₀ : Prop) : Prop :=
  (¬total₀)

@[qualif]
def EqZero (total₀ : Int) : Prop :=
  (total₀ = 0)

@[qualif]
def GtZero (total₀ : Int) : Prop :=
  (total₀ > 0)

@[qualif]
def GeZero (total₀ : Int) : Prop :=
  (total₀ ≥ 0)

@[qualif]
def LtZero (total₀ : Int) : Prop :=
  (total₀ < 0)

@[qualif]
def LeZero (total₀ : Int) : Prop :=
  (total₀ ≤ 0)

@[qualif]
def Eq (total₀ : Int) (i₀ : Int) : Prop :=
  (total₀ = i₀)

@[qualif]
def Gt (total₀ : Int) (i₀ : Int) : Prop :=
  (total₀ > i₀)

@[qualif]
def Ge (total₀ : Int) (i₀ : Int) : Prop :=
  (total₀ ≥ i₀)

@[qualif]
def Lt (total₀ : Int) (i₀ : Int) : Prop :=
  (total₀ < i₀)

@[qualif]
def Le (total₀ : Int) (i₀ : Int) : Prop :=
  (total₀ ≤ i₀)

@[qualif]
def Le1 (total₀ : Int) (i₀ : Int) : Prop :=
  (total₀ ≤ (i₀ - 1))

end FibSumLoopQualifs

open FibSumLoopQualifs

set_option maxHeartbeats 5000000
#time def FibSumLoop_proof : FibSumLoop := by
  unfold FibSumLoop
  solve_fixpoint_combo

end F
