import Lean
import Aesop
import LeanFixpoint.Tactic.Internal.Utils

open Lean Meta Elab Tactic

-- Attempt to prove
def checkExprVC (prop : Expr) : TermElabM Bool := do
  let mvar   ← mkFreshExprMVar (some prop) (kind := .syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      evalTactic (← `(tactic|
        (intros
         first
           | omega
           | grind
          --  | (simp_all; grind)
          -- | aesop
           | (constructor <;> grind))))
    return goals.isEmpty
  catch _ =>
    return false
