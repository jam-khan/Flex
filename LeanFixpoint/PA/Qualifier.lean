import Lean

open Lean Meta

initialize qualifAttr : TagAttribute ←
  registerTagAttribute `qualif "marks a definition as a refinement type qualifier for predicate abstraction."

-- Get all defs tagged as `@[qualif]`
def getQualifiers : MetaM (Array Expr) := do
  let names := qualifAttr.ext.getState (← getEnv)
  names.toArray.mapM fun n => do
    mkConstWithLevelParams n

-- Instantiate a qualifier by β-reduction.
-- Unfolds ONLY the qualifier's own lambda (via `unfoldDefinition?`) and then
-- collapses the resulting redex with `headBeta`. We deliberately avoid `whnf`
-- because it would further unfold relations like `≤` into their kernel defs
-- (e.g. `(b - a).NonNeg`), producing unreadable trace output.
def Expr.instQualifier (q : Expr) (args : Array Expr) : MetaM Expr := do
  let applied := mkAppN q args
  match ← unfoldDefinition? applied with
  | some unfolded => return unfolded.headBeta
  | none          => return applied
