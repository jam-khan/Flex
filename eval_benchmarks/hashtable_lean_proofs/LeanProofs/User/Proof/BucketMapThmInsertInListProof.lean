import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BucketMapThmInsertInList
open Classical
set_option linter.unusedVariables false


namespace F

namespace BucketMapThmInsertInListQualifs

@[qualif]
def EqTrue (ls_res₀ : Prop) : Prop :=
  ls_res₀

@[qualif]
def EqFalse (ls_res₀ : Prop) : Prop :=
  (¬ls_res₀)

@[qualif]
def EqZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ = 0)

@[qualif]
def GtZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ > 0)

@[qualif]
def GeZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ ≥ 0)

@[qualif]
def LtZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ < 0)

@[qualif]
def LeZero (ls_res₀ : Int) : Prop :=
  (ls_res₀ ≤ 0)

@[qualif]
def Eq (ls_res₀ : Int) (inserted₀ : Int) : Prop :=
  (ls_res₀ = inserted₀)

@[qualif]
def Gt (ls_res₀ : Int) (inserted₀ : Int) : Prop :=
  (ls_res₀ > inserted₀)

@[qualif]
def Ge (ls_res₀ : Int) (inserted₀ : Int) : Prop :=
  (ls_res₀ ≥ inserted₀)

@[qualif]
def Lt (ls_res₀ : Int) (inserted₀ : Int) : Prop :=
  (ls_res₀ < inserted₀)

@[qualif]
def Le (ls_res₀ : Int) (inserted₀ : Int) : Prop :=
  (ls_res₀ ≤ inserted₀)

@[qualif]
def Le1 (ls_res₀ : Int) (inserted₀ : Int) : Prop :=
  (ls_res₀ ≤ (inserted₀ - 1))

end BucketMapThmInsertInListQualifs

open BucketMapThmInsertInListQualifs

set_option maxHeartbeats 5000000
#time def BucketMapThmInsertInList_proof : BucketMapThmInsertInList := by
  unfold BucketMapThmInsertInList
  solve_fixpoint_combo

end F
