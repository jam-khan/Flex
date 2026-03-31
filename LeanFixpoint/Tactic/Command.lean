import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Solve.Solver
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Elab.FromExpr


open Lean Elab Meta Command Tactic

elab "#inspect_prop" t:term : command => do
  liftTermElabM do
    let expr ← Term.elabTerm t (some (mkSort levelZero))

    let reduced ← reduce expr
    logInfo m!"Reduced Expr:\n{reduced}"
    dbg_trace "Reduced raw: {toString reduced}"   -- raw, no pretty print

    let expr ← instantiateMVars expr
    let whnfExpr ← whnf expr
    logInfo m!"WHNF:\n{whnfExpr}"
    dbg_trace "WHNF raw: {toString whnfExpr}"     -- raw, no pretty print

elab "#translate_and_solve" t:term : command => do
  liftTermElabM do
    let expr ← Term.elabTerm t (some (mkSort levelZero))
    let reduced ← reduce expr

    -- Phase 1: Expr → PropAST
    let fvarsRef ← IO.mkRef ({} : FVarMap)
    let kvarsRef ← IO.mkRef ({} : KVarSet)
    let propAST ← toPropASTWithTracking fvarsRef kvarsRef reduced
    let fvarMap ← fvarsRef.get
    let kvarSet ← kvarsRef.get

    -- Phase 2: PropAST → Constraint
    let constraint ← toConstraint fvarMap kvarSet propAST
    logInfo m!"Translated Constraint:\n{toString constraint}"

    -- Phase 3: Solve
    solveAndCheckConstraint constraint

elab "#test_manual_assignment" : command => do
  Lean.Elab.Command.liftTermElabM do
    let flats := mixedAfterAcyclic.flat

    -- Build assignment: κd ↦ (0 ≤ z)
    let sol : Pred := .rexpr (.cmp .le (.int 0) (.var `z))
    let mut assignment : Std.HashMap KVar Pred := {}
    assignment := assignment.insert kd sol
    -- Check only the κd-related flat constraints
    let kdFlats := flats.filter fun fc =>
      fc.kvars.any (· == kd)

    logInfo m!"κd-related flat constraints: {kdFlats.length}"

    for fc in kdFlats do
      logInfo m!"Checking: {toString fc.val}"
      let ok ← checkFlatUnderAssignment fc assignment
      if ok then
        logInfo m!"  ✅ valid"
      else
        logWarning m!"❌ invalid"

-- #test_manual_assignment
