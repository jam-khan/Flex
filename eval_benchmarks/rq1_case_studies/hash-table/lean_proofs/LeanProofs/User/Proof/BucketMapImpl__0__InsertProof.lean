import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__Insert
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0InsertQualifs

@[qualif]
def EqTrue (new_slf₀ : Prop) : Prop :=
  new_slf₀

@[qualif]
def EqFalse (new_slf₀ : Prop) : Prop :=
  (¬new_slf₀)

@[qualif]
def EqZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ = 0)

@[qualif]
def GtZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ > 0)

@[qualif]
def GeZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ ≥ 0)

@[qualif]
def LtZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ < 0)

@[qualif]
def LeZero (new_slf₀ : Int) : Prop :=
  (new_slf₀ ≤ 0)

@[qualif]
def Eq (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ = a'₁)

@[qualif]
def Gt (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ > a'₁)

@[qualif]
def Ge (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ ≥ a'₁)

@[qualif]
def Lt (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ < a'₁)

@[qualif]
def Le (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ ≤ a'₁)

@[qualif]
def Le1 (new_slf₀ : Int) (a'₁ : Int) : Prop :=
  (new_slf₀ ≤ (a'₁ - 1))

end BucketMapImpl0InsertQualifs

open BucketMapImpl0InsertQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__Insert_proof : BucketMapImpl__0__Insert := by
  unfold BucketMapImpl__0__Insert
  solve_fixpoint_combo

end F
