import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VectorsTest1
open Classical
set_option linter.unusedVariables false


namespace F

namespace VectorsTest1Qualifs

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

end VectorsTest1Qualifs

open VectorsTest1Qualifs

set_option maxHeartbeats 5000000
#time def VectorsTest1_proof : VectorsTest1 := by
  unfold VectorsTest1
  solve_fixpoint_combo

end F
