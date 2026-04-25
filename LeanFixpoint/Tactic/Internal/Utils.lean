import Lean

open Lean Elab Tactic

/--
  Run `tactic` and report whether it succeeded
  or not. On failure, roll back the tactic state
  to avoid leakage of partial state mutations.
-/
def attemptTactic (tactic : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  try
    tactic
    return true
  catch _ =>
    saved.restore
    return false
