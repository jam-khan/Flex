-- import Lean

-- import Aesop
-- import LeanFixpoint.Solve.Solver
-- import LeanFixpoint.Elab.ToExpr
-- import LeanFixpoint.Tactic.Utils

-- open Lean Meta Elab Term Tactic

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

-- -- TODO: weakenOnce and solveFixpoint/predicateAbstraction need Qualifier
-- -- (deferred until Qualifier.lean is migrated from RExpr → Expr)
