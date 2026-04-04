import Lean

import Aesop
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Subst
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Solve.Qualifier
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Tactic.Utils

open Lean Meta Elab Term Tactic

-- Build Pred (conjunction of qualifiers) from a list of RExpr
def conjoinQualifiers (qs : List RExpr) : Pred :=
  match qs.map Pred.rexpr with
  | []      => Pred.tru
  | [p]     => p
  | p :: ps => ps.foldl Pred.conj p

-- Extract actual args from κ-application in head
def getHeadArgs : Pred → KVar → List Var
  | .kapp k args, κ => if k == κ then args else []
  | .conj p₁ p₂, κ => getHeadArgs p₁ κ ++ getHeadArgs p₂ κ
  | _, _ => []

-- Replace κ's formal params with actual args in a qualifier -/
def instantiateQualWithArgs (κ : KVar) (q : RExpr) (args : List Var) : RExpr :=
  -- constructs a parameter × argument pair
  -- where paramᵢ is to be replaced by argᵢ
  let pairs := κ.params.zip args
  pairs.foldl (fun acc (param, arg) => RExpr.subst param (.var arg) acc) q

def checkConstraintVC (c : Constraint) : TermElabM Bool := do
  let prop ← c.toExpr {}
  let mvar ← mkFreshExprMVar (some prop) (kind := MetavarKind.syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      -- try the full closer chain from SolveFixpoint
      let _ ← attemptTactic (evalTactic (← `(tactic | simp_all)))
      let _ ← attemptTactic (evalTactic (← `(tactic | grind)))
      let _ ← attemptTactic (evalTactic (← `(tactic | omega)))
      let _ ← attemptTactic (evalTactic (← `(tactic | aesop)))
    return goals.isEmpty
  catch _ => return Bool.false

-- Single weakening pass
-- Essentially takes constraints and qualifiers, tried to substitute a qualifier till satisfaction
def weakenOnce
    (flatCs : List FlatConstraint)
    (assignment : List (KVar × List RExpr))
    : TermElabM (List (KVar × List RExpr)) := do
  let mut κq_pairs := assignment
  for fc in flatCs do
    for κ in fc.head.kvars do
      -- take out the ones with κ in kappa qualifier pairs
      let some qs := (κq_pairs.find? fun (κ', _) => κ' == κ).map (·.2)
        | continue
      -- get head arguments from κ application in head
      let headArgs := getHeadArgs fc.head κ
      -- qualifiers list
      let mut kept : List RExpr := []

      -- loop through qualifiers
      for q in qs do
        -- get constraint from the flattened constraint
        let mut c := fc.val
        -- walk through pair of kappa and corresponding qualifiers
        for (k, kqs) in κq_pairs do
          -- perform elimination using the qualifiers for k
          c := c.elimStar k (conjoinQualifiers kqs)
        -- instantiate qualifier q with headargs from κ in flattened constraint fc
        let qInst := instantiateQualWithArgs κ q headArgs
        -- now, elimstart with this instantiation
        c := c.elimStar κ (.rexpr qInst)
        -- check if constraint is satisfied
        let ok ← checkConstraintVC c
        -- if sat, then keep qualifier
        if ok then kept := kept ++ [q]
      κq_pairs := κq_pairs.map fun (k, qs') => if k == κ then (k, kept) else (k, qs')
  return κq_pairs

-- Iterate until fixpoint
-- NOTE: CHECK this carefully again
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
    let qs := Q.map fun q => q.instantiate κ.params
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
