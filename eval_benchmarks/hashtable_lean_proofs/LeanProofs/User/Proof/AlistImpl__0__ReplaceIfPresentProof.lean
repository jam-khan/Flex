import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.AlistImpl__0__ReplaceIfPresent
open Classical
set_option linter.unusedVariables false


namespace F

namespace AlistImpl0ReplaceIfPresentQualifs

@[qualif]
def EqTrue (k₁ : Prop) : Prop :=
  k₁

@[qualif]
def EqFalse (k₁ : Prop) : Prop :=
  (¬k₁)

@[qualif]
def EqZero (k₁ : Int) : Prop :=
  (k₁ = 0)

@[qualif]
def GtZero (k₁ : Int) : Prop :=
  (k₁ > 0)

@[qualif]
def GeZero (k₁ : Int) : Prop :=
  (k₁ ≥ 0)

@[qualif]
def LtZero (k₁ : Int) : Prop :=
  (k₁ < 0)

@[qualif]
def LeZero (k₁ : Int) : Prop :=
  (k₁ ≤ 0)

@[qualif]
def Eq (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ = t₀)

@[qualif]
def Gt (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ > t₀)

@[qualif]
def Ge (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ ≥ t₀)

@[qualif]
def Lt (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ < t₀)

@[qualif]
def Le (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ ≤ t₀)

@[qualif]
def Le1 (k₁ : Int) (t₀ : Int) : Prop :=
  (k₁ ≤ (t₀ - 1))

end AlistImpl0ReplaceIfPresentQualifs

open AlistImpl0ReplaceIfPresentQualifs

set_option maxHeartbeats 5000000
#time def AlistImpl__0__ReplaceIfPresent_proof : AlistImpl__0__ReplaceIfPresent := by
  unfold AlistImpl__0__ReplaceIfPresent
  (try zap) ; (try simp [*]) ; (try solve)

end F
