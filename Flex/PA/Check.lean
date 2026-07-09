import Lean
import Aesop
import Flex.Tactic.Utils

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

def proveLeaf (goal : Expr) : TermElabM (Option Expr) := withSilencedMessages do
  let mvar   ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      evalTactic (← `(tactic|
        (first
          | omega
          | grind
          | (constructor <;> grind))))
    if !goals.isEmpty then return none
    let proof ← instantiateMVars mvar
    if proof.hasSorry || proof.hasExprMVar then return none
    return some proof
  catch _ =>
    return none

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
