import Lean

import LeanFixpoint.Solve.Weakening

open Lean Meta Elab Term Tactic

-- Iterate until fixpoint
partial def solveFixpoint
    (flatCs : List FlatConstraint)
    (assignment : List (KVar × List RExpr))
    : TermElabM (List (KVar × List RExpr)) := do
  let a' ← weakenOnce flatCs assignment
  let changed := a'.zip assignment |>.any fun ((_, qs'), (_, qs)) =>
    qs'.length != qs.length
  if !changed then return a'
  solveFixpoint flatCs a'

-- predicate abstraction
def predicateAbstraction (c : Constraint) (Q : List Qualifier)
  : TermElabM (List (KVar × List RExpr)) := do

  -- Log the constraint received
  logInfo m!"[predicate-abstraction] Received constraint:\n{toString c}"

  -- Log qualifiers
  let qStrs := Q.map fun q =>
    let ps := String.intercalate ", " (q.params.map fun p => s!"{p.sym} : {toString p.sort}")
    s!"{q.name}({ps} | {toString q.body})"
  logInfo m!"[predicate-abstraction] Qualifiers ({Q.length}):\n{String.intercalate "\n" (qStrs.map (s!" · " ++ · ))}"

  -- Partition κ-vars
  let (acyclic, cyclic) := c.partitionKVars

  -- Log acyclic status
  if acyclic.isEmpty then
    logInfo m!"[oredicate-abstraction] No acyclic κ-vars remaining (fusion handled them all)"
  else
    logWarning m!"[predicate-abstraction] Acyclic κ-vars still present (fusion missed these): {acyclic.map (·.name)}"

  -- Log cyclic κ-vars
  if cyclic.isEmpty then
    logInfo m!"[predicate-abstraction] No cyclic κ-vars -- nothing to solve"
    return [] -- since no cyclic kvars to solve for predicate abstraction

  logInfo m!"[predicate-abstraction] Cyclic κ-vars to solve: {cyclic.map (·.name)}"

  -- Flatten constraint
  let flatCs := c.flat

  -- Initialize: each cylic κ gets all qualifiers instantiates with its params
  let init := cyclic.map fun κ =>
    let qs := Q.flatMap fun q =>
      let perms := kPerms q.params.length κ.params
      perms.map fun perm => q.instantiate perm
    (κ, qs)

  -- Display κ with instantiated qualifiers
  for (κ, qs) in init do
    logInfo m!"[predicate-abstraction] Init A({κ.name}) ↦ {qs.map toString}"

  -- Solve fixpoint
  let assignment ← solveFixpoint flatCs init

  -- Final κ assignment/solutions after pedicate abstraction
  for (κ, qs) in assignment do
    logInfo m!"[predicate-abstraction] Final A({κ.name}) ↦ {qs.map toString}"

  return assignment
