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

-- def checkConstraintVC (c : Constraint) : TermElabM Bool := do
--   -- Build env from local context so UFs are available
--   let mut env : VarMap := {}
--   let lctx ← getLCtx
--   for decl in lctx do
--     if !decl.isAuxDecl then
--       env := env.insert decl.userName (mkFVar decl.fvarId)
--   let prop ← c.toExpr env
--   let mvar ← mkFreshExprMVar (some prop) (kind := MetavarKind.syntheticOpaque)
--   let mvarId := mvar.mvarId!
--   try
--     let goals ← Tactic.run mvarId do
--       let _ ← attemptTactic (evalTactic (← `(tactic | omega)))
--       let _ ← attemptTactic (evalTactic (← `(tactic | grind)))
--     logInfo m!"[checkVC] result={goals.isEmpty} remaining={goals.length} prop={prop}"
--     return goals.isEmpty
--   catch e =>
--     logInfo m!"[checkVC] EXCEPTION: {e.toMessageData}"
--     return Bool.false

-- -- Single weakening pass
-- --
-- -- For each flat clause with κ in the head, test each qualifier q:
-- --   1. Substitute ALL κ-vars (including current) with full assignment
-- --      → body κ-apps get the conjunction, head κ-app becomes `true`
-- --   2. Replace the `true` head with q[params→headArgs]
-- --   3. Check the VC: body[A] ⇒ q[headArgs]
-- def weakenOnce
--     (flatCs : List FlatConstraint)
--     (assignment : List (KVar × List RExpr))
--     : TermElabM (List (KVar × List RExpr)) := do
--   let mut κq_pairs := assignment
--   logInfo m!"[weakenOnce] flatCs count={flatCs.length}"
--   for fc in flatCs do
--     let headKvars := fc.head.kvars
--     logInfo m!"[weakenOnce] fc head kvars={headKvars.map (·.name)}"
--     for κ in headKvars do
--       let some qs := (κq_pairs.find? fun (κ', _) => κ' == κ).map (·.2)
--         | continue
--       let headArgs := getHeadArgs fc.head κ
--       logInfo m!"[weakenOnce] κ={κ.name} headArgs={headArgs} qs.length={qs.length}"
--       let mut kept : List RExpr := []
--       for q in qs do
--         let mut c := fc.val
--         for (k, kqs) in κq_pairs do
--           c := c.elimStar k (conjoinQualifiers kqs)
--         -- ADD THIS LINE:
--         logInfo m!"[weakenOnce] after elimStar:\n{toString c}"
--         -- Replace `true` head with q instantiated at head args.
--         let qBody := RExpr.substMany κ.params headArgs q
--         let qRepr := repr q
--         let qBodyRepr := repr qBody
--         logInfo m!"[weakenOnce] q repr={qRepr}"
--         logInfo m!"[weakenOnce] qBody repr={qBodyRepr}"
--         logInfo m!"[weakenOnce] leaf BEFORE replace:\n{toString c}"
--         c := replaceLeafPred c (.rexpr qBody)
--         logInfo m!"[weakenOnce] leaf AFTER replace:\n{toString c}"
--         let ok ← checkConstraintVC c
--         logInfo m!"[weakenOnce] q={toString q} ok={ok}"
--         if ok then kept := kept ++ [q]
--       logInfo m!"[weakenOnce] κ={κ.name} kept={kept.map toString}"
--       κq_pairs := κq_pairs.map fun (k, qs') => if k == κ then (k, kept) else (k, qs')
--   return κq_pairs
