import Lean
import LeanFixpoint.Solve.Qualifier

open Lean Meta

@[qualif]
def _test_q_le (a : Int) (b : Int) : Prop := a ≤ b

@[qualif]
def _test_q_pos (v : Int) : Prop := 0 ≤ v

#eval show MetaM Unit from do
  let qs ← getQualifiers
  for q in qs do
    let ty ← inferType q
    let ci ← getConstInfo q.constName!
    IO.println s!" {q} : {← ppExpr ty}"
    if let some val := ci.value? then
      IO.println s!"    = {← ppExpr val}"

