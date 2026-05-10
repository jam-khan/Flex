import Lean
import Std

open Lean Meta Elab Tactic

partial def evalEraseDupsExpr (e : Expr) : MetaM Expr := do
  transform e fun subterm => do
    if subterm.isAppOf ``List.eraseDups then
      let reduced ← whnf subterm
      return .done (← instantiateMVars reduced)
    else
      return .continue

elab "simp_scopes" : tactic => do
  liftMetaTactic fun goal => do
    let target ← goal.getType
    let target' ← evalEraseDupsExpr target

    if target == target' then
      pure [goal]
    else
      let eqProof ← mkEqRefl target'
      let newGoal ← goal.replaceTargetEq target' eqProof
      pure [newGoal]
