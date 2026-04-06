import Lean

open Lean Elab Meta Command Tactic

def attemptTactic (t : TacticM Unit) : TacticM Bool :=
  tryCatch (do t; pure Bool.true) (fun _ => pure Bool.false)
