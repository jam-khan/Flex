import Lean

import LeanFixpoint.Monad
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Solve.Qualifier

open Lean Meta Elab Term Tactic

-- Simply, take [e₁, ... , eₙ] where eᵢ
-- and turn it into (e₁ ∧ ...) ∧ eₙ
def conjoinExprs : List Expr → Expr
  | []  => mkConst ``True
  | [e] => e
  | e :: es => es.foldl (fun acc x => mkApp2 (mkConst ``And) acc x) e

partial def specializeClauseForHead
    (headKVar   : KVar)
    (q          : Expr)            -- qualifier lambda (unapplied, e.g. `q_le`)
    (qSlots     : List Nat)        -- slot mapping: qualifier-param i → κ-slot qSlots[i]
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr := do
  let e ← whnf e
  if e.isForall then
    -- elim* hypothesis substitution: walk κ's and substitute in bindingDomain
    let mut dom := e.bindingDomain! -- body of forall (∀)
    for (κ, sol) in assignment do
      dom := substKVarInExpr κ sol dom
    withLocalDeclD e.bindingName! dom fun fvar => do
      let body  := e.bindingBody!.instantiate1 fvar
      let body' ← specializeClauseForHead headKVar q qSlots assignment body
      let abstr := body'.abstract #[fvar]
      -- once all substitutions are done with κ-vars
      -- then, we create a new `∀` and return it
      pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
  else if let some (l, r) := e.and? then
    -- if there is `∧`
    let l' ← specializeClauseForHead headKVar q qSlots assignment l
    let r' ← specializeClauseForHead headKVar q qSlots assignment r
    return mkApp2 (mkConst ``And) l' r'
  else
    -- Leaf: is it the head κ-app?
    let fn := e.getAppFn
    if fn.isFVar && fn.fvarId! == headKVar.fvarId then
      -- Head position: β-apply q to the head args projected by qSlots.
      -- `e.getAppArgs` contains the actual κ-args at this call site
      -- (in the lctx established by outer `withLocalDeclD`s);
      -- `qSlots` picks out which of those go to which qualifier param.
      let args   := e.getAppArgs
      let chosen := (qSlots.map fun i => args[i]!).toArray
      liftM (Expr.instQualifier q chosen)
    else
      -- Non-κ leaf: hypothesis-position substitution for any embedded κ-app
      let mut acc := e
      for (κ, sol) in assignment do
        acc := substKVarInExpr κ sol acc
      return acc
