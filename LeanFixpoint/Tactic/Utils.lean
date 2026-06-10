import Lean

open Lean Elab Tactic

/-- When `true`, the solver tactics emit a per-phase heartbeat delta line
    `[phase] <tac>:<phase>=<hb/1000>` to stdout (consumed by the RQ3 eval
    harness). Off by default so normal builds / regression stay quiet. -/
register_option leanfixpoint.benchPhases : Bool := {
  defValue := false
  descr    := "Emit per-phase heartbeat deltas for the RQ3 evaluation."
}

/-- Measure the heartbeats consumed by `act` and, iff
    `leanfixpoint.benchPhases` is set, print `[phase] <tac>:<phase>=<hb/1000>`.
    Generic over the tactic/meta monad (needs options + IO lifting). -/
@[inline] def benchPhase {m : Type → Type} {α : Type}
    [Monad m] [MonadLiftT IO m] [MonadOptions m]
    (tac phase : String) (act : m α) : m α := do
  if leanfixpoint.benchPhases.get (← getOptions) then
    let h0 ← (IO.getNumHeartbeats : IO Nat)
    let r ← act
    let h1 ← (IO.getNumHeartbeats : IO Nat)
    (IO.println s!"[phase] {tac}:{phase}={(h1 - h0) / 1000}" : IO Unit)
    pure r
  else
    act

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
