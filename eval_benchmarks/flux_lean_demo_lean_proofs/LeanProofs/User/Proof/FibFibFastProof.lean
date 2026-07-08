import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast
open Classical
set_option linter.unusedVariables false


namespace F

namespace FibFibFastQualifs

@[qualif]
def EqTrue (prev₀ : Prop) : Prop :=
  prev₀

@[qualif]
def EqFalse (prev₀ : Prop) : Prop :=
  (¬prev₀)

@[qualif]
def EqZero (prev₀ : Int) : Prop :=
  (prev₀ = 0)

@[qualif]
def GtZero (prev₀ : Int) : Prop :=
  (prev₀ > 0)

@[qualif]
def GeZero (prev₀ : Int) : Prop :=
  (prev₀ ≥ 0)

@[qualif]
def LtZero (prev₀ : Int) : Prop :=
  (prev₀ < 0)

@[qualif]
def LeZero (prev₀ : Int) : Prop :=
  (prev₀ ≤ 0)

@[qualif]
def Eq (prev₀ : Int) (curr₀ : Int) : Prop :=
  (prev₀ = curr₀)

@[qualif]
def Gt (prev₀ : Int) (curr₀ : Int) : Prop :=
  (prev₀ > curr₀)

@[qualif]
def Ge (prev₀ : Int) (curr₀ : Int) : Prop :=
  (prev₀ ≥ curr₀)

@[qualif]
def Lt (prev₀ : Int) (curr₀ : Int) : Prop :=
  (prev₀ < curr₀)

@[qualif]
def Le (prev₀ : Int) (curr₀ : Int) : Prop :=
  (prev₀ ≤ curr₀)

@[qualif]
def Le1 (prev₀ : Int) (curr₀ : Int) : Prop :=
  (prev₀ ≤ (curr₀ - 1))

end FibFibFastQualifs

open FibFibFastQualifs

set_option maxHeartbeats 5000000
#time def FibFibFast_proof : FibFibFast := by
  unfold FibFibFast
  (try zap) ; (try simp [*]) ; (try solve)

end F
