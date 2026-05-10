import Lean

open Lean Elab Tactic

/--
  Run `tactic` and report whether it succeeded
  or not. On failure, roll back the tactic state
  AND restore the Core message log so any errors
  the tactic logged before throwing don't leak —
  `saveState`/`saved.restore` only cover Term/Meta
  state, not the message log.
-/
def attemptTactic (tactic : TacticM Unit) : TacticM Bool := do
  let saved     ← saveState
  let savedMsgs ← Core.getMessageLog
  try
    tactic
    return true
  catch _ =>
    saved.restore
    Core.setMessageLog savedMsgs
    return false
