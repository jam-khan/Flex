import Lean
import Aesop
import LeanFixpoint.Tactic.Utils

open Lean Meta Elab Tactic

-- Run `k` and discard any messages it logs (errors, warnings, traces).
-- PA candidate-checking calls `grind`/`omega`/etc. inside `first`-style
-- ladders; failed branches log diagnostics that survive plain `try/catch`
-- because they go through Lean's message log, not the exception path.
-- We snapshot the log before, restore it after, regardless of outcome.
private def withSilencedMessages {α} (k : TermElabM α) : TermElabM α := do
  let saved ← Core.getMessageLog
  try
    let r ← k
    Core.setMessageLog saved
    return r
  catch e =>
    Core.setMessageLog saved
    throw e

-- Attempt to prove `prop` via the standard tactic ladder.
-- Returns `true` iff all goals are closed AND the resulting proof term
-- contains no `sorry`. Lean's `(constructor <;> grind)` silently uses
-- `sorry` for unsolved sub-goals, so `goals.isEmpty` alone is unsound:
-- `Tactic.run` reports goals=0, mvar.isAssigned=true, but the proof has
-- `sorry` inside.
def checkExprVC (prop : Expr) : TermElabM Bool := withSilencedMessages do
  let mvar   ← mkFreshExprMVar (some prop) (kind := .syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      evalTactic (← `(tactic|
        (intros
         first
           | omega
           | grind
           -- `aesop` drives `simp` normalization that unfolds recursive
           -- `@[grind]` defs (e.g. `fib_spec_fib`) without bound; the
           -- resulting `maxRecDepth` is logged as a diagnostic rather than
           -- thrown, so `withSilencedMessages`/`try` can't swallow it and it
           -- fails the whole build. It also over-weakens PA solutions on
           -- several benchmarks (12 regressions when enabled). Keep dropped.
           | (constructor <;> grind))))
    if !goals.isEmpty then return false
    let proof ← instantiateMVars mvar
    return !proof.hasSorry
  catch _ =>
    return false

-- Sat-guard for PA: returns `true` iff the LHS hypothesis of the
-- implication-shaped `propWithFalseConclusion` is contradictory — i.e.
-- the same clause but with the conclusion replaced by `False` is provable.
-- Caller passes a goal whose head leaf has already been replaced with
-- `False` (via `specializeClauseAsNeg`).
def checkExprUnsat (propWithFalseConclusion : Expr) : TermElabM Bool := withSilencedMessages do
  let mvar   ← mkFreshExprMVar (some propWithFalseConclusion) (kind := .syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      evalTactic (← `(tactic|
        (intros
         first
           | omega
           | grind
           | (constructor <;> grind))))
    if !goals.isEmpty then return false
    let proof ← instantiateMVars mvar
    return !proof.hasSorry
  catch _ =>
    return false
