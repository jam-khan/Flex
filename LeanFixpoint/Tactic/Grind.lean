-- import Lean
-- import LeanFixpoint.Core.Types
-- import LeanFixpoint.Core.Fusion
-- import LeanFixpoint.Elab.ToExpr

-- /-!
--   # Metaprogramming code using `grind` to discharge.
-- -/

-- open Lean Meta Elab Term Tactic

-- /--
--   Try to discharge a κ-free constraint using `grind`.

--   Returns `true` if `grind` closes the goal, `false` otherwise.
--   Useful for testing the pipeline end-to-end.
-- -/
-- def checkVCWithGrindOmega (c : Constraint) : TermElabM Bool := do
--   let prop ← c.toExpr {}
--   let propTy ← inferType prop
--   unless (← isDefEq propTy (mkSort .zero)) do
--     throwError s!"checkVC: elaborated expression is not a Prop"
--   let mvar ← mkFreshExprMVar (some prop) (kind := MetavarKind.syntheticOpaque)
--   let mvarId := mvar.mvarId!
--   try
--     let goals ← Tactic.run mvarId do
--       evalTactic (← `(tactic| first | grind | omega))
--     return goals.isEmpty
--   catch _ =>
--     return Bool.false

-- def solveAndCheckConstraint (c : Constraint) : TermElabM Unit := do
--     let kvars : List KVar := c.kvars.eraseDups
--     if kvars.isEmpty then
--       logInfo m!"No κ-variables found, constraint is already a VC."
--     else
--       logInfo m!"κ-variables: {kvars.map toString}"

--     let mut eliminated := c
--     for κ in kvars do
--       let sol := eliminated.sol1 κ
--       logInfo m!"  {κ.name}({κ.params.map toString}) = {toString sol}"
--       eliminated := eliminated.elim1 κ

--     logInfo m!"Eliminated constraint:\n{toString eliminated}"

--     let prop ← eliminated.toExpr {}
--     let fmt ← ppExpr prop
--     logInfo m!"VC: {fmt}"

--     let ok ← checkVCWithGrindOmega eliminated
--     if ok then
--       logInfo m!"✅ VC discharged successfully"
--     else
--       logWarning m!"❌ VC could not be discharged by omega or grind"

-- /--
--   `#solve_constraint c` solves for all κ-variables in constraint `c`,
--   eliminates them, and tries to discharge the resulting VC with omega/grind.

--   Pipeline:
--   - Infer κ-variables via `c.kvars`
--   - Solve each κ via `sol1` and eliminate via `elim1`
--   - Elaborate the κ-free constraint to a Prop
--   - Discharge with `omega` or `grind`

--   Usage:
-- ```
--   #solve_constraint exConstraint
-- ```

--   Output:
-- ```
--   κ-variables: [κ2, κk]
--     κ2([k]) = 0 ≤ ν ∧ k ≤ ν
--     κk([k]) = ⊤
--   Eliminated constraint: ...
--   VC: ∀ k : Int, k < 0 → 0 ≤ 0 ∧ k ≤ 0
--   ✅ VC discharged successfully
-- ```
-- -/
-- elab "#solve_constraint " t:term : command => do
--   Lean.Elab.Command.liftTermElabM do
--     let elabExprC ← Lean.Elab.Term.elabTerm t (some (mkConst ``Constraint))
--     let elabExprC ← instantiateMVars elabExprC
--     let c ← try
--       unsafe Lean.Meta.evalExpr Constraint (mkConst ``Constraint) elabExprC
--     catch _ =>
--       throwError s!"Reflection failed"
--     solveAndCheckConstraint c

-- /--
--   `checkFlatUnderAssignment` takes a FlatConstraint, and
--   an assignment, which is a mapping from `kvars` to `predicates`.
--   Then, it iteratively eliminates each `kvar` using `elimStar`
--   in the constraint.

--   After iteratively eliminating all `kvar`,
--   it checks if result is valid under assignment
-- -/
-- def checkFlatUnderAssignment
--     (fc : FlatConstraint)
--     (assignment : Std.HashMap KVar Pred)
--     : TermElabM Bool := do
--   let mut c := fc.val
--   for (κ, sol) in assignment.toList do
--     c := c.elimStar κ sol
--   checkVCWithGrindOmega c

-- section Test

-- -- Using mixed test from `Constraint.lean`
-- #eval do
--   let flats := mixedAfterAcyclic.flat
--   IO.println s!"Number of flat constraints: {flats.length}"
--   for (i, fc) in flats.toArray.mapIdx (·, ·) |>.toList do
--     IO.println s!"\n--- Flat constraint {i} ---"
--     IO.println (toString fc.val)
--     IO.println s!"  head kvars: {fc.head.kvars.map toString}"
--     IO.println s!"  body kvars: {(fc.body.map Pred.kvars).flatten.map toString}"

-- end Test
