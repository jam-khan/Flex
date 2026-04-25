import Lean
import Aesop

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Monad

open Lean Elab Meta Tactic
private partial def closeLoop : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => pure ()
  | g :: restGoals =>
    let ty ← whnfR (← g.getType)
    if ty.isForall then
      evalTactic (← `(tactic| intro _))
      closeLoop
    else if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| and_intros))
      closeLoop
    else
      let closers := #[
        `(tactic| omega),
        `(tactic| grind),
        `(tactic| aesop),
        `(tactic| (constructor <;> grind)),
        `(tactic| (simp_all; grind))
      ]
      let mut closed := false
      for c in closers do
        if !closed then
          let b ← attemptTactic (evalTactic (← c))
          if b then closed := true
      if closed then
        closeLoop
      else
        setGoals restGoals
        closeLoop
        let remaining ← getGoals
        setGoals (g :: remaining)
