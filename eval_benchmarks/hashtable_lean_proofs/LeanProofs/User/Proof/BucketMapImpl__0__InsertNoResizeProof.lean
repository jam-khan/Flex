import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapImpl__0__InsertNoResize
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapImpl0InsertNoResizeQualifs

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
def Eq (a'₀ : Int) (ls_res₀ : Int) : Prop :=
  (a'₀ = ls_res₀)

@[qualif]
def Gt (a'₀ : Int) (ls_res₀ : Int) : Prop :=
  (a'₀ > ls_res₀)

@[qualif]
def Ge (a'₀ : Int) (ls_res₀ : Int) : Prop :=
  (a'₀ ≥ ls_res₀)

@[qualif]
def Lt (a'₀ : Int) (ls_res₀ : Int) : Prop :=
  (a'₀ < ls_res₀)

@[qualif]
def Le (a'₀ : Int) (ls_res₀ : Int) : Prop :=
  (a'₀ ≤ ls_res₀)

@[qualif]
def Le1 (a'₀ : Int) (ls_res₀ : Int) : Prop :=
  (a'₀ ≤ (ls_res₀ - 1))

end BucketMapImpl0InsertNoResizeQualifs

open BucketMapImpl0InsertNoResizeQualifs

set_option maxHeartbeats 5000000
#time def BucketMapImpl__0__InsertNoResize_proof : BucketMapImpl__0__InsertNoResize := by
  unfold BucketMapImpl__0__InsertNoResize
  (try zap) ; (try simp [*]) ; (try solve)

end F
