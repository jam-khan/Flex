import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortQuicksortRange
open Classical
set_option linter.unusedVariables false


namespace F

namespace SortQuicksortRangeQualifs

@[qualif]
def EqTrue (p₀ : Prop) : Prop :=
  p₀

@[qualif]
def EqFalse (p₀ : Prop) : Prop :=
  (¬p₀)

@[qualif]
def EqZero (p₀ : Int) : Prop :=
  (p₀ = 0)

@[qualif]
def GtZero (p₀ : Int) : Prop :=
  (p₀ > 0)

@[qualif]
def GeZero (p₀ : Int) : Prop :=
  (p₀ ≥ 0)

@[qualif]
def LtZero (p₀ : Int) : Prop :=
  (p₀ < 0)

@[qualif]
def LeZero (p₀ : Int) : Prop :=
  (p₀ ≤ 0)

@[qualif]
def Eq (p₀ : Int) (v₀ : Int) : Prop :=
  (p₀ = v₀)

@[qualif]
def Gt (p₀ : Int) (v₀ : Int) : Prop :=
  (p₀ > v₀)

@[qualif]
def Ge (p₀ : Int) (v₀ : Int) : Prop :=
  (p₀ ≥ v₀)

@[qualif]
def Lt (p₀ : Int) (v₀ : Int) : Prop :=
  (p₀ < v₀)

@[qualif]
def Le (p₀ : Int) (v₀ : Int) : Prop :=
  (p₀ ≤ v₀)

@[qualif]
def Le1 (p₀ : Int) (v₀ : Int) : Prop :=
  (p₀ ≤ (v₀ - 1))

end SortQuicksortRangeQualifs

open SortQuicksortRangeQualifs

set_option maxHeartbeats 5000000
#time def SortQuicksortRange_proof : SortQuicksortRange := by
  unfold SortQuicksortRange
  (try zap) ; (try simp [*]) ; (try solve)

end F
