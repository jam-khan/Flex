import Lean
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Qualifier
import MetaRefinementTypes.Elab

open Lean Meta Elab Term Tactic

/-- Build Pred (conjunction of qualifiers) from a list of RExpr -/
def conjoinQualifiers (qs : List RExpr) : Pred :=
  match qs.map Pred.rexpr with
  | []      => Pred.tru
  | [p]     => p
  | p :: ps => ps.foldl Pred.conj p

/-- Replace κ's formal params with actual args in a qualifier -/
def instantiateQualWithArgs (κ : KVar) (q : RExpr) (args : List Var) : RExpr :=
  let pairs := κ.params.zip args
  pairs.foldl (fun acc (param, arg) => RExpr.subst param (.var arg) acc) q

/-- Extract actual args from κ-application in head -/
def getHeadArgs : Pred → KVar → List Var
  | .kapp k args, κ => if k == κ then args else []
  | .conj p₁ p₂, κ => getHeadArgs p₁ κ ++ getHeadArgs p₂ κ
  | _, _ => []

/-- One weakening pass -/
def weakenOnce
    (flatCs : List FlatConstraint)
    (assignment : List (KVar × List RExpr))
    : TermElabM (List (KVar × List RExpr)) := do
  let mut a := assignment
  for fc in flatCs do
    for κ in fc.head.kvars do
      let some qs := (a.find? fun (k, _) => k == κ).map (·.2)
        | continue
      let headArgs := getHeadArgs fc.head κ
      let mut kept : List RExpr := []
      for q in qs do
        -- Substitute all κ in body with current assignment
        let mut c := fc.val
        for (k, kqs) in a do
          c := c.elimStar k (conjoinQualifiers kqs)
        -- Substitute head κ with this specific qualifier
        let qInst := instantiateQualWithArgs κ q headArgs
        c := c.elimStar κ (.rexpr qInst)
        -- Check
        let ok ← checkVCWithGrindOmega c
        if ok then kept := kept ++ [q]
      -- Update assignment for κ
      a := a.map fun (k, qs') => if k == κ then (k, kept) else (k, qs')
  return a

/-- Iterate until fixpoint -/
partial def solveFixpoint
    (flatCs : List FlatConstraint)
    (assignment : List (KVar × List RExpr))
    : TermElabM (List (KVar × List RExpr)) := do
  let a' ← weakenOnce flatCs assignment
  let changed := a'.zip assignment |>.any fun ((_, qs'), (_, qs)) =>
    qs'.length != qs.length
  if !changed then return a'
  solveFixpoint flatCs a'

/-- Full sat: Fusion + predicate abstraction -/
def sat (c : Constraint) (Q : List Qualifier) : TermElabM Bool := do
  let (acyclic, cuts) := c.partitionKVars
  let c' := c.elim acyclic
  if cuts.isEmpty then
    checkVCWithGrindOmega c'
  else
    let flatCs := c'.flat
    -- Initialize: each cyclic κ gets all qualifiers
    let init := cuts.map fun κ =>
      let qs := Q.map fun q => q.instantiate κ.params.head!
      (κ, qs)
    -- Iterate
    let assignment ← solveFixpoint flatCs init
    -- Substitute final solution
    let mut result := c'
    for (κ, qs) in assignment do
      result := result.elimStar κ (conjoinQualifiers qs)
    checkVCWithGrindOmega result


/--
  `#solve_constraint_full c` — Fusion + predicate abstraction.

  1. Partition κ-vars into acyclic/cyclic
  2. Eliminate acyclic via Fusion
  3. If cyclic remain, run predicate abstraction with given qualifiers
  4. Elaborate and discharge with grind/omega
-/
elab "#solve_constraint_full " t:term " with " qt:term : command => do
  Lean.Elab.Command.liftTermElabM do
    -- Reflect constraint
    let cExpr ← Lean.Elab.Term.elabTerm t (some (mkConst ``Constraint))
    let cExpr ← instantiateMVars cExpr
    let c ← try
      unsafe Lean.Meta.evalExpr Constraint (mkConst ``Constraint) cExpr
    catch _ => throwError "Failed to reflect Constraint"

    -- Reflect qualifier list
    let qExpr ← Lean.Elab.Term.elabTerm qt
      (some (mkApp (mkConst ``List [.zero]) (mkConst ``Qualifier)))
    let qExpr ← instantiateMVars qExpr
    let Q ← try
      unsafe Lean.Meta.evalExpr (List Qualifier)
        (mkApp (mkConst ``List [.zero]) (mkConst ``Qualifier)) qExpr
    catch _ => throwError "Failed to reflect qualifier list"

    -- Phase 1: partition
    let (acyclic, cuts) := c.partitionKVars
    logInfo m!"Acyclic: {acyclic.map toString}"
    logInfo m!"Cyclic:  {cuts.map toString}"

    -- Phase 2: Fusion
    let mut eliminated := c
    for κ in acyclic do
      let sol := eliminated.sol1 κ
      logInfo m!"  sol1({κ.name}) = {toString sol}"
      eliminated := eliminated.elim1 κ

    -- Phase 3: predicate abstraction (if cyclic vars remain)
    if cuts.isEmpty then
      logInfo m!"No cyclic variables."
    else
      let flatCs := eliminated.flat
      -- Initialize
      let init := cuts.map fun κ =>
        let qs := Q.map fun q => q.instantiate κ.params.head!
        (κ, qs)
      for (κ, qs) in init do
        logInfo m!"  Init A({κ.name}) = {qs.map toString}"

      -- Solve fixpoint
      let assignment ← solveFixpoint flatCs init
      for (κ, qs) in assignment do
        logInfo m!"  Final A({κ.name}) = {qs.map toString}"

      -- Substitute
      for (κ, qs) in assignment do
        let sol := conjoinQualifiers qs
        eliminated := eliminated.elimStar κ sol

    -- Phase 4: elaborate and check
    logInfo m!"Final constraint:\n{toString eliminated}"
    let prop ← eliminated.toExpr {}
    let fmt ← ppExpr prop
    logInfo m!"VC: {fmt}"
    let ok ← checkVCWithGrindOmega eliminated
    if ok then logInfo m!"✅ VC discharged"
    else logWarning m!"❌ VC could not be discharged"

section Test
/-- Simple test command -/
elab "#test_sat" : command => do
  Lean.Elab.Command.liftTermElabM do
    let Q : List Qualifier := [
      { pred := r{ 0 ≤ v } },
      { pred := r{ v ≤ 0 } }
    ]
    let ok ← sat mixedTest Q
    if ok then logInfo m!"✅ sat returned true"
    else logWarning m!"❌ sat returned false"

#test_sat

end Test
