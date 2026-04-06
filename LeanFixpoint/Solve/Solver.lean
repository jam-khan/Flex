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

/-- All ordered k-tuples drawn from `xs` (with no repeats) -/
partial def kPerms [BEq α] (k : Nat) (xs : List α) : List (List α) :=
  if k == 0 then [[]]
  else xs.flatMap fun x =>
    (kPerms (k-1) (xs.erase x)).map (x :: ·)

-- Replace κ's formal params with actual args in a qualifier -/
def instantiateQualWithArgs (κ : KVar) (q : RExpr) (args : List Var) : RExpr :=
  -- constructs a parameter × argument pair
  -- where paramᵢ is to be replaced by argᵢ
  let pairs := κ.params.zip args
  pairs.foldl (fun acc (param, arg) => RExpr.subst param (.var arg) acc) q

def checkConstraintVC (c : Constraint) : TermElabM Bool := do
  -- Build env from local context so UFs are available
  let mut env : VarMap := {}
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isAuxDecl then
      env := env.insert decl.userName (mkFVar decl.fvarId)
  let prop ← c.toExpr env
  -- let prop ← c.toExpr {}
  let mvar ← mkFreshExprMVar (some prop) (kind := MetavarKind.syntheticOpaque)
  let mvarId := mvar.mvarId!
  try
    let goals ← Tactic.run mvarId do
      -- try the full closer chain from SolveFixpoint
      -- let _ ← attemptTactic (evalTactic (← `(tactic | simp_all)))
      let _ ← attemptTactic (evalTactic (← `(tactic | omega)))
      let _ ← attemptTactic (evalTactic (← `(tactic | grind)))
      -- let _ ← attemptTactic (evalTactic (← `(tactic | aesop)))
    logInfo m!"[checkVC] result={goals.isEmpty} remaining={goals.length} prop={prop}"
    return goals.isEmpty
  catch e =>
    logInfo m!"[checkVC] EXCEPTION: {e.toMessageData}"
    return Bool.false

/-- Replace the leaf predicate in a flat constraint (head position) -/
def replaceLeafPred : Constraint → Pred → Constraint
  | .pred _, p => .pred p
  | .imp x b hyp c, p => .imp x b hyp (replaceLeafPred c p)
  | .conj _ _, _ => .pred .tru  -- shouldn't happen on flat constraints

-- Single weakening pass
--
-- For each flat clause with κ in the head, test each qualifier q:
--   1. Substitute ALL κ-vars (including current) with full assignment
--      → body κ-apps get the conjunction, head κ-app becomes `true`
--   2. Replace the `true` head with q[params→headArgs]
--   3. Check the VC: body[A] ⇒ q[headArgs]
def weakenOnce
    (flatCs : List FlatConstraint)
    (assignment : List (KVar × List RExpr))
    : TermElabM (List (KVar × List RExpr)) := do
  let mut κq_pairs := assignment
  logInfo m!"[weakenOnce] flatCs count={flatCs.length}"
  for fc in flatCs do
    let headKvars := fc.head.kvars
    logInfo m!"[weakenOnce] fc head kvars={headKvars.map (·.name)}"
    for κ in headKvars do
      let some qs := (κq_pairs.find? fun (κ', _) => κ' == κ).map (·.2)
        | continue
      let headArgs := getHeadArgs fc.head κ
      logInfo m!"[weakenOnce] κ={κ.name} headArgs={headArgs} qs.length={qs.length}"
      let mut kept : List RExpr := []
      for q in qs do
        let mut c := fc.val
        -- Substitute ALL κ-vars with their full assignment conjunction.
        -- Body κ-apps: applyKVarSol maps formal params to actual args.
        -- Head κ-app: becomes `true` (elimStar behaviour).
        for (k, kqs) in κq_pairs do
          c := c.elimStar k (conjoinQualifiers kqs)
        -- Replace `true` head with q instantiated at head args.
        let qBody := RExpr.substMany κ.params headArgs q
        let qRepr := repr q
        let qBodyRepr := repr qBody
        logInfo m!"[weakenOnce] q repr={qRepr}"
        logInfo m!"[weakenOnce] qBody repr={qBodyRepr}"
        logInfo m!"[weakenOnce] leaf BEFORE replace:\n{toString c}"
        c := replaceLeafPred c (.rexpr qBody)
        logInfo m!"[weakenOnce] leaf AFTER replace:\n{toString c}"
        let ok ← checkConstraintVC c
        logInfo m!"[weakenOnce] q={toString q} ok={ok}"
        if ok then kept := kept ++ [q]
      logInfo m!"[weakenOnce] κ={κ.name} kept={kept.map toString}"
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
