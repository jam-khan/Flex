import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortTest1
open Classical
set_option linter.unusedVariables false


namespace F

namespace SortTest1Qualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (new₀ : Int) : Prop :=
  (v₀ = new₀)

@[qualif]
def Gt (v₀ : Int) (new₀ : Int) : Prop :=
  (v₀ > new₀)

@[qualif]
def Ge (v₀ : Int) (new₀ : Int) : Prop :=
  (v₀ ≥ new₀)

@[qualif]
def Lt (v₀ : Int) (new₀ : Int) : Prop :=
  (v₀ < new₀)

@[qualif]
def Le (v₀ : Int) (new₀ : Int) : Prop :=
  (v₀ ≤ new₀)

@[qualif]
def Le1 (v₀ : Int) (new₀ : Int) : Prop :=
  (v₀ ≤ (new₀ - 1))

end SortTest1Qualifs

open SortTest1Qualifs

set_option maxHeartbeats 5000000
#time def SortTest1_proof : SortTest1 := by
  unfold SortTest1
  solve_fixpoint_combo

end F
