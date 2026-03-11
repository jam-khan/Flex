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
