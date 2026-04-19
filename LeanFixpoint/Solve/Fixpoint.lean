import Lean

import LeanFixpoint.Monad
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Solve.Instantiation
import LeanFixpoint.Solve.Weaken

open Lean Meta Elab Term Tactic

/-- Build the initial Houdini assignment: every cyclic κ maps to the union
    of every `@[qualif]`-tagged lambda instantiated over every type-compatible
    ordered slot-tuple of `κ.paramTypes`.

    For 4-arg `k0` with 4 tagged qualifiers, this produces on the order of
    4 + 12 + 12 + 12 = 40 candidates. -/
def buildInitialAssignment (cyclicKs : List KVar)
    : MetaM (List (KVar × List (Expr × List Nat))) := do
  let qs ← getQualifiers
  cyclicKs.mapM fun κ => do
    let mut cands : List (Expr × List Nat) := []
    for q in qs do
      let instantiations ← instantiateQualifier q κ.paramTypes
      cands := cands ++ instantiations.toList
    return (κ, cands)

/-- Iterate `weakenOnce` until the total candidate count across all κ's stops
    shrinking. Monotone: the total count is strictly decreasing per iteration
    until the fixpoint, so termination is guaranteed given finite candidates. -/
partial def solveFixpoint
    (kctx       : KContext)
    (flatCs     : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  let next ← weakenOnce kctx flatCs assignment
  let beforeCount := assignment.foldl (fun acc (_, cs) => acc + cs.length) 0
  let afterCount  := next.foldl       (fun acc (_, cs) => acc + cs.length) 0
  if afterCount == beforeCount then
    return next
  else
    solveFixpoint kctx flatCs next

/-- Turn the final Houdini assignment into one `Expr` per κ, ready for witness
    synthesis. Per κ, β-apply every surviving candidate at κ's canonical fvar
    placeholders (`FVarId.mk "z0"`, …), then conjoin.

    Output shape matches what `solToWitnessExpr` in `Elab/ToExpr.lean` expects. -/
def finalizeSolutions (assignment : List (KVar × List (Expr × List Nat)))
    : MetaM (List (KVar × Expr)) := do
  assignment.mapM fun (κ, cands) => do
    let paramFvars : Array Expr :=
      (κ.params.map fun n => Expr.fvar (FVarId.mk n)).toArray
    let bodies ← cands.mapM fun (q, slots) => do
      let chosen : Array Expr := (slots.map fun i => paramFvars[i]!).toArray
      Expr.instQualifier q chosen
    return (κ, conjoinExprs bodies)

/-- One-shot PA: from cyclic κ list + flat constraint + κ-context, run the full
    Houdini pipeline and return the final solution Expr per κ.

    Typical caller:  after fusion has eliminated acyclic κ's, hand the still-
    cyclic κ's and the residual flat clauses to this function. -/
def predicateAbstraction
    (kctx     : KContext)
    (cyclicKs : List KVar)
    (flatCs   : List Expr)
    : TermElabM (List (KVar × Expr)) := do
  let initial ← buildInitialAssignment cyclicKs
  let fixed   ← solveFixpoint kctx flatCs initial
  finalizeSolutions fixed

-- import Lean

-- import LeanFixpoint.Solve.Weakening

-- open Lean Meta Elab Term Tactic

-- -- Iterate until fixpoint
-- partial def solveFixpoint
--     (flatCs : List FlatConstraint)
--     (assignment : List (KVar × List RExpr))
--     : TermElabM (List (KVar × List RExpr)) := do
--   let a' ← weakenOnce flatCs assignment
--   let changed := a'.zip assignment |>.any fun ((_, qs'), (_, qs)) =>
--     qs'.length != qs.length
--   if !changed then return a'
--   solveFixpoint flatCs a'

-- -- predicate abstraction
-- def predicateAbstraction (c : Constraint) (Q : List Qualifier)
--   : TermElabM (List (KVar × List RExpr)) := do

--   -- Log the constraint received
--   logInfo m!"[predicate-abstraction] Received constraint:\n{toString c}"

--   -- Log qualifiers
--   let qStrs := Q.map fun q =>
--     let ps := String.intercalate ", " (q.params.map fun p => s!"{p.sym} : {toString p.sort}")
--     s!"{q.name}({ps} | {toString q.body})"
--   logInfo m!"[predicate-abstraction] Qualifiers ({Q.length}):\n{String.intercalate "\n" (qStrs.map (s!" · " ++ · ))}"

--   -- Partition κ-vars
--   let (acyclic, cyclic) := c.partitionKVars

--   -- Log acyclic status
--   if acyclic.isEmpty then
--     logInfo m!"[oredicate-abstraction] No acyclic κ-vars remaining (fusion handled them all)"
--   else
--     logWarning m!"[predicate-abstraction] Acyclic κ-vars still present (fusion missed these): {acyclic.map (·.name)}"

--   -- Log cyclic κ-vars
--   if cyclic.isEmpty then
--     logInfo m!"[predicate-abstraction] No cyclic κ-vars -- nothing to solve"
--     return [] -- since no cyclic kvars to solve for predicate abstraction

--   logInfo m!"[predicate-abstraction] Cyclic κ-vars to solve: {cyclic.map (·.name)}"

--   -- Flatten constraint
--   let flatCs := c.flat

--   -- Initialize: each cylic κ gets all qualifiers instantiates with its params
--   let init := cyclic.map fun κ =>
--     let qs := Q.flatMap fun q =>
--       let perms := kPerms q.params.length κ.params
--       perms.map fun perm => q.instantiate perm
--     (κ, qs)

--   -- Display κ with instantiated qualifiers
--   for (κ, qs) in init do
--     logInfo m!"[predicate-abstraction] Init A({κ.name}) ↦ {qs.map toString}"

--   -- Solve fixpoint
--   let assignment ← solveFixpoint flatCs init

--   -- Final κ assignment/solutions after pedicate abstraction
--   for (κ, qs) in assignment do
--     logInfo m!"[predicate-abstraction] Final A({κ.name}) ↦ {qs.map toString}"

--   return assignment
