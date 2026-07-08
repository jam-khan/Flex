import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMergeSort
open Classical
set_option linter.unusedVariables false


namespace F

namespace SortMergeSortQualifs

@[qualif]
def EqTrue (aux₀ : Prop) : Prop :=
  aux₀

@[qualif]
def EqFalse (aux₀ : Prop) : Prop :=
  (¬aux₀)

@[qualif]
def EqZero (aux₀ : Int) : Prop :=
  (aux₀ = 0)

@[qualif]
def GtZero (aux₀ : Int) : Prop :=
  (aux₀ > 0)

@[qualif]
def GeZero (aux₀ : Int) : Prop :=
  (aux₀ ≥ 0)

@[qualif]
def LtZero (aux₀ : Int) : Prop :=
  (aux₀ < 0)

@[qualif]
def LeZero (aux₀ : Int) : Prop :=
  (aux₀ ≤ 0)

@[qualif]
def Eq (aux₀ : Int) (aux₁ : Int) : Prop :=
  (aux₀ = aux₁)

@[qualif]
def Gt (aux₀ : Int) (aux₁ : Int) : Prop :=
  (aux₀ > aux₁)

@[qualif]
def Ge (aux₀ : Int) (aux₁ : Int) : Prop :=
  (aux₀ ≥ aux₁)

@[qualif]
def Lt (aux₀ : Int) (aux₁ : Int) : Prop :=
  (aux₀ < aux₁)

@[qualif]
def Le (aux₀ : Int) (aux₁ : Int) : Prop :=
  (aux₀ ≤ aux₁)

@[qualif]
def Le1 (aux₀ : Int) (aux₁ : Int) : Prop :=
  (aux₀ ≤ (aux₁ - 1))

end SortMergeSortQualifs

open SortMergeSortQualifs

set_option maxHeartbeats 5000000
#time def SortMergeSort_proof : SortMergeSort := by
  unfold SortMergeSort
  (try zap) ; (try simp [*]) ; (try solve)

end F
