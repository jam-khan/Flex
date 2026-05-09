import Lean

import LeanFixpoint.Monad
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Solve.Check

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

/-- One iteration of Houdini weakening.

    For each flat clause whose conclusion is a κ-application:
    · Identify the head κ.
    · For each candidate `(q, qSlots)` currently assigned to that κ,
      specialize the clause — substitute hypothesis κ-apps by their current
      conjunctive solution, and replace the head leaf with `q` β-applied at
      the head-args projected by `qSlots`.
    · Check the resulting VC via `checkExprVC`. Keep candidate iff it passes.

    Returns the updated assignment (with failed candidates dropped). Monotone:
    `kept ⊆ original` for every κ. -/
partial def weakenOnce
    (kctx       : KContext)
    (flatCs     : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  -- Pre-materialize one `currentSol` Expr per κ for hypothesis-position
  -- substitution. Each candidate is β-applied at κ.params' canonical-fvar
  -- placeholders, then conjoined. `substKVarInExpr` later re-substitutes
  -- those placeholders with actual κ-app args at each hypothesis site.
  let currentSols : List (KVar × Expr) ← assignment.mapM fun (κ, cands) => do
    -- create fvars for the parameters of the `κ`
    let paramFvars : Array Expr :=
      (κ.params.map fun n => Expr.fvar (FVarId.mk n)).toArray
    -- here, we map through each candidate qualifier
    -- for each `q`, we take the qualifier `q`
    -- and create a β-reduced `Expr` body by applying combination of args
    -- why? let's say qualifier has two params but 4 args are being passed
    -- then, naturally some goes to waste and some need combination.
    let bodies ← cands.mapM fun (q, slots) => do
      let chosen : Array Expr := (slots.map fun i => paramFvars[i]!).toArray
      Expr.instQualifier q chosen
    -- after getting all β-reduced kappas we return the conjoined expression
    -- overall the bodies
    return (κ, conjoinExprs bodies)
  -- Iterate flat clauses, weakening the head κ's candidate list
  -- this is initial assignment of κ ↦ solutions
  -- that gets mutated as the algorithm runs and performing weakening
  let mut out := assignment
  -- take one flat clause
  for fc in flatCs do
    -- return head κ if found inside the head of `∀`-chain inside `fc`
    let some headKVar ← (findHeadKVar fc).run kctx | continue
    -- find if there is an assignment for `headKVar` in the `assignment`
    let some (_, candidates) := out.find? (·.1 == headKVar) | continue
    -- now, iterate through the `κ` qualifiers from the candidates
    let mut kept : List (Expr × List Nat) := []
    for (q, slots) in candidates do
      -- specialize clause with that κ and current solutions
      -- note: below performs κ specialization for all the clauses
      let vc ← (specializeClauseForHead headKVar q slots currentSols fc).run kctx
      let vcFmt ← ppExpr vc
      let qFmt ← ppExpr q
      IO.println s!"[weakenOnce] head={headKVar.name} slots={slots} q={qFmt} vc={vcFmt}"
      if ← checkExprVC vc then
        IO.println s!"[weakenOnce] KEEPING IT"
        kept := kept.concat (q, slots)
    out := out.map fun (κ, qs) =>
      if κ == headKVar then (κ, kept) else (κ, qs)

  return out
