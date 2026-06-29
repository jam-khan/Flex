import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortInsert
open Classical
set_option linter.unusedVariables false


namespace F

namespace SortInsertQualifs

@[qualif]
def EqTrue (k₀ : Prop) : Prop :=
  k₀

@[qualif]
def EqFalse (k₀ : Prop) : Prop :=
  (¬k₀)

@[qualif]
def EqZero (k₀ : Int) : Prop :=
  (k₀ = 0)

@[qualif]
def GtZero (k₀ : Int) : Prop :=
  (k₀ > 0)

@[qualif]
def GeZero (k₀ : Int) : Prop :=
  (k₀ ≥ 0)

@[qualif]
def LtZero (k₀ : Int) : Prop :=
  (k₀ < 0)

@[qualif]
def LeZero (k₀ : Int) : Prop :=
  (k₀ ≤ 0)

@[qualif]
def Eq (k₀ : Int) (a'₁ : Int) : Prop :=
  (k₀ = a'₁)

@[qualif]
def Gt (k₀ : Int) (a'₁ : Int) : Prop :=
  (k₀ > a'₁)

@[qualif]
def Ge (k₀ : Int) (a'₁ : Int) : Prop :=
  (k₀ ≥ a'₁)

@[qualif]
def Lt (k₀ : Int) (a'₁ : Int) : Prop :=
  (k₀ < a'₁)

@[qualif]
def Le (k₀ : Int) (a'₁ : Int) : Prop :=
  (k₀ ≤ a'₁)

@[qualif]
def Le1 (k₀ : Int) (a'₁ : Int) : Prop :=
  (k₀ ≤ (a'₁ - 1))

end SortInsertQualifs

open SortInsertQualifs

set_option maxHeartbeats 5000000
#time def SortInsert_proof : SortInsert := by
  unfold SortInsert
  solve_fixpoint_combo

end F
