import Lean

import LeanFixpoint.Fusion.Types
import LeanFixpoint.Monad
import LeanFixpoint.Fusion.Utils
import LeanFixpoint.Fusion.Flatten

open Lean Meta

-- Dependencies for a single flat clause: (body κ, head κ) pairs.
partial def exprFlatDeps (e : Expr) : KM (List (KVar × KVar)) := do
  let (bodyKs, headKs) ← go e
  return bodyKs.flatMap fun kb => headKs.map fun kh => (kb, kh)
where
  go (e : Expr) : KM (List KVar × List KVar) := do
    let e ← whnf e
    if e.isForall then
      withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
        let domKs ← KM.exprKVars e.bindingDomain!
        let (bodyKs, headKs) ← go (e.bindingBody!.instantiate1 fvar)
        return (domKs ++ bodyKs, headKs)
    else
      return ([], ← KM.exprKVars e)

-- Dependencies for an `Expr`: flatten then compute deps on each piece.
def exprDeps (e : Expr) : KM (List (KVar × KVar)) := do
  let flats ← exprFlat e
  let deps ← flats.mapM exprFlatDeps
  return deps.flatten

/-- Dependencies excluding pairs that involve any κ in `K`. -/
def exprDepsExcluding (e : Expr) (K : List KVar) : KM (List (KVar × KVar)) := do
  let deps ← exprDeps e
  return deps.filter fun (k1, k2) => !K.contains k1 && !K.contains k2

/-- Collect κ-vars from an Expr in left-to-right depth-first order,
    matching the traversal order of `Constraint.kvars`. -/
partial def exprKVarsOrdered (e : Expr) : KM (List KVar) := do
  let e ← whnf e
  if let some (l, r) := e.and? then
    return (← exprKVarsOrdered l) ++ (← exprKVarsOrdered r)
  else if e.isForall then
    let dom := e.bindingDomain!
    let domKs ← KM.exprKVars dom
    withLocalDeclD e.bindingName! dom fun fvar => do
      let bodyKs ← exprKVarsOrdered (e.bindingBody!.instantiate1 fvar)
      return domKs ++ bodyKs
  else
    KM.exprKVars e

/-- κ-vars reachable from `start` via 1+ dep edges.
    `deps` convention: `(u, v) ∈ deps` ⟺ u in body, v in head ⟹ edge u → v. -/
private partial def reachableFrom
    (start : KVar) (deps : List (KVar × KVar)) : List KVar :=
  let succs (k : KVar) : List KVar :=
    deps.filterMap fun (u, v) => if u == k then some v else none
  let rec dfs (visited : List KVar) (frontier : List KVar) : List KVar :=
    match frontier with
    | []      => visited
    | x :: xs =>
      if visited.contains x then dfs visited xs
      else dfs (x :: visited) (succs x ++ xs)
  dfs [] (succs start)

/-- κ is cyclic iff it lies on any directed cycle in the dep graph
    (self-loop or longer cycle through other κ's). -/
def exprIsCyclic (κ : KVar) (e : Expr) : KM Bool := do
  let deps ← exprDeps e
  return (reachableFrom κ deps).contains κ

/-- Topologically sort the acyclic κ-vars so dependency sinks come first.
    If `(u, v) ∈ deps` (u in body where v in head), then u must be eliminated
    before v so v's sol doesn't leak a free reference to u. -/
partial def topoSortAcyclic (acyclic : List KVar) (deps : List (KVar × KVar)) :
    List KVar :=
  let rec go (remaining : List KVar) (acc : List KVar) : List KVar :=
    match remaining with
    | [] => acc.reverse
    | _ =>
      -- Pick κ with no predecessor in `remaining`: no `(κ', κ) ∈ deps`
      -- such that κ' is still in `remaining` and κ' ≠ κ.
      let ready? := remaining.find? fun κ =>
        !deps.any fun (u, v) => v == κ && u != κ && remaining.contains u
      match ready? with
      | some κ => go (remaining.filter (· != κ)) (κ :: acc)
      | none   => acc.reverse ++ remaining  -- cycle in "acyclic" (shouldn't happen)
  go acyclic []

-- IMPLEMENTATION OF SCC Algorithm

private structure TarjanState where
  nextIdx   : Nat       := 0
  stack     : List KVar := []
  onStack   : List KVar := []
  indexMap  : List (KVar × Nat) := []
  lowMap    : List (KVar × Nat) := []
  sccs      : List (List KVar)  := []

private def tsGetIdx (s : TarjanState) (k : KVar) : Option Nat :=
  (s.indexMap.find? fun (k', _) => k' == k).map (·.2)

private def tsGetLow (s : TarjanState) (k : KVar) : Nat :=
  ((s.lowMap.find? fun (k', _) => k' == k).map (·.2)).getD 0

private def tsSetLow (s : TarjanState) (k : KVar) (v : Nat) : TarjanState :=
  { s with lowMap := s.lowMap.map fun (k', n) =>
      if k' == k then (k', v) else (k', n) }

-- Pop stack until `k` is found (inclusive). Returns (scc, remainingStack)
private def tsPopUntil (stack : List KVar) (k : KVar) :
    List KVar × List KVar :=
  let rec go (rest : List KVar) (scc : List KVar) :=
    match rest with
    | []      => (scc, [])
    | x :: xs =>
        if x == k
        then (k :: scc, xs)
        else go xs (x :: scc)
  go stack []

private partial def strongConnect
    (k : KVar) (succs : KVar → List KVar)
    (s : TarjanState) : TarjanState :=
  let s := { s with
    indexMap  := (k, s.nextIdx) :: s.indexMap
    lowMap    := (k, s.nextIdx) :: s.lowMap
    nextIdx   := s.nextIdx + 1
    stack     := k :: s.stack
    onStack   := k :: s.onStack
    }
  let s := (succs k).foldl (fun s w =>
    match tsGetIdx s w with
    | none =>
      let s := strongConnect w succs s
      tsSetLow s k (min (tsGetLow s k) (tsGetLow s w))
    | some _ =>
      if s.onStack.contains w then
        let wIdx := (tsGetIdx s w).getD 0
        tsSetLow s k (min (tsGetLow s k) wIdx)
      else s
  ) s
  if tsGetLow s k == (tsGetIdx s k).getD 0 then
    let (scc, remaining) := tsPopUntil s.stack k
    { s with
      stack   := remaining
      onStack := s.onStack.filter fun x => !scc.contains x
      sccs    := scc :: s.sccs }
  else s

-- Tarjan's SCC, reverse topological order.
def tarjanSCC (nodes : List KVar) (edges : List (KVar × KVar)) :
    List (List KVar) :=
  let succs (k : KVar) : List KVar :=
    edges.filterMap fun (u, v) => if u == k then some v else none
  let s := nodes.foldl (fun s k =>
    if (tsGetIdx s k).isSome then s
    else strongConnect k succs s
  ) {}
  s.sccs

-- Does this κ have a self-loop?
def hasSelfLoop (k : KVar) (edges : List (KVar × KVar)) : Bool :=
  edges.any fun (u, v) => u == k && v == k

-- Iteratively remove high-degree nodes and recompute SCCs
-- until all SCCs are singletons without self-loops.
partial def cutVarsIterative (nodes : List KVar)
    (edges : List (KVar × KVar)) : List KVar :=
  let sccs := tarjanSCC nodes edges
  let cyclicSCC := sccs.find? fun scc =>
    scc.length > 1 || (scc.length == 1 && hasSelfLoop scc.head! edges)
  match cyclicSCC with
  | none     => []
  | some scc =>
    let pick := scc.foldl (fun best k =>
      let deg := edges.filter (fun (u, v) =>
        (u == k || v == k) && scc.contains u && scc.contains v) |>.length
      match best with
      | none => some (k, deg)
      | some (_, bd) => if deg > bd then some (k, deg) else best
    ) none |>.map (·.1) |>.getD scc.head!
    let remainingNodes := nodes.filter (· != pick)
    let remainingEdges := edges.filter fun (u, v) => u != pick && v != pick
    pick :: cutVarsIterative remainingNodes remainingEdges

-- Classify all κ-vars into (acyclicInTopoOrder, cyclic)
def classifyKVars (allKs : List KVar) (deps : List (KVar × KVar)) :
    List KVar × List KVar :=
  let khat := cutVarsIterative allKs deps
  let acyclic := allKs.filter fun k => !khat.contains k
  let acyclicDeps := deps.filter fun (u, v) =>
    acyclic.contains u && acyclic.contains v
  let acyclicSorted := topoSortAcyclic acyclic acyclicDeps
  (acyclicSorted, khat)

-------------------------------------------------------
-- Testing
-------------------------------------------------------

-- Check deps match expected edges given as (srcIndex, tgtIndex) into kvars array.
private def checkDeps (name : String) (kvars : Array KVar)
    (deps : List (KVar × KVar)) (expected : List (Nat × Nat)) : MetaM Unit := do
  let expectedEdges := expected.map fun (i, j) => (kvars[i]!.mvarId, kvars[j]!.mvarId)
  let actualEdges := deps.map fun (b, h) => (b.mvarId, h.mvarId)
  if actualEdges.length != expectedEdges.length then
    logInfo m!"FAIL [{name}]: expected {repr expectedEdges.length} edges, got {repr actualEdges.length}"
    return
  let allOk := expectedEdges.all fun e => actualEdges.contains e
  if allOk then
    logInfo m!"PASS [{name}]"
  else
    logInfo m!"FAIL [{name}]: wrong edges"

-- Create a κ-var (mvar of type `Int → Prop`) and its KVar record.
private def mkTestKVar (n : Name) : MetaM (KVar × Expr) := do
  let intTy  := mkConst ``Int
  let propTy := mkSort levelZero
  let kTy    ← mkArrow intTy propTy
  let mvar   ← mkFreshExprMVar kTy (userName := n)
  let kvar : KVar := {
    name       := n
    mvarId     := mvar.mvarId!
    params     := []
    paramTypes := []
  }
  return (kvar, mvar)

private def runFlatDeps (kvars : List KVar) (e : Expr) :
    MetaM (List (KVar × KVar)) :=
  let hm := kvars.foldl (fun acc k => acc.insert k.mvarId k) {}
  let ctx : KContext := { kvars := hm }
  (exprFlatDeps e).run ctx

-- Test 1: κ₁(x) → κ₂(x)
--   one body guard, one head
--   expected edges: [(κ₁, κ₂)]
#eval! show MetaM Unit from do
  let (kv1, k1) ← mkTestKVar `κ₁
  let (kv2, k2) ← mkTestKVar `κ₂
  let kvars := #[kv1, kv2]
  let e ← withLocalDeclD `x (mkConst ``Int) fun x => do
    mkForallFVars #[x] (← mkArrow (mkApp k1 x) (mkApp k2 x))
  let deps ← runFlatDeps kvars.toList e
  checkDeps "κ₁(x) → κ₂(x)" kvars deps [(0, 1)]

-- Test 2: ∀ x : Int, κ₁(x) → κ₃(x) → κ₂(x)
--   value binder + two body guards, one head
--   expected edges: [(κ₁, κ₂), (κ₃, κ₂)]
#eval! show MetaM Unit from do
  let (kv1, k1) ← mkTestKVar `κ₁
  let (kv2, k2) ← mkTestKVar `κ₂
  let (kv3, k3) ← mkTestKVar `κ₃
  let kvars := #[kv1, kv2, kv3]
  let e ← withLocalDeclD `x (mkConst ``Int) fun x => do
    mkForallFVars #[x] (← mkArrow (mkApp k1 x) (← mkArrow (mkApp k3 x) (mkApp k2 x)))
  let deps ← runFlatDeps kvars.toList e
  checkDeps "∀ x, κ₁(x) → κ₃(x) → κ₂(x)" kvars deps [(0, 1), (2, 1)]

-- Test: exprDeps on (κ₁(x) → κ₂(x)) ∧ (κ₃(x) → κ₂(x))
-- flatten produces two clauses, deps unions their edges
-- expected: [(κ₁, κ₂), (κ₃, κ₂)]
#eval! show MetaM Unit from do
  let (kv1, k1) ← mkTestKVar `κ₁
  let (kv2, k2) ← mkTestKVar `κ₂
  let (kv3, k3) ← mkTestKVar `κ₃
  let kvars := #[kv1, kv2, kv3]
  let e ← withLocalDeclD `x (mkConst ``Int) fun x => do
    let cl1 ← mkArrow (mkApp k1 x) (mkApp k2 x)
    let cl2 ← mkArrow (mkApp k3 x) (mkApp k2 x)
    mkForallFVars #[x] (mkApp2 (mkConst ``And) cl1 cl2)
  let deps ← (exprDeps e).run { kvars := kvars.toList.foldl (fun acc k => acc.insert k.mvarId k) {} }
  checkDeps "exprDeps: (κ₁→κ₂) ∧ (κ₃→κ₂)" kvars deps [(0, 1), (2, 1)]

-- Test: linear chain κ₁ → κ₂ → κ₃ (all acyclic)
#eval! show MetaM Unit from do
  let (kv1, _) ← mkTestKVar `κ₁
  let (kv2, _) ← mkTestKVar `κ₂
  let (kv3, _) ← mkTestKVar `κ₃
  let (acyclic, cyclic) := classifyKVars [kv1, kv2, kv3] [(kv1, kv2), (kv2, kv3)]
  if cyclic.length == 0 && acyclic.length == 3 then
    logInfo m!"PASS [linear chain: all acyclic]"
  else
    logInfo m!"FAIL [linear]: cyclic={repr cyclic.length}, acyclic={repr acyclic.length}"

-- Test: cycle κ₁ ↔ κ₂, plus standalone κ₃
#eval! show MetaM Unit from do
  let (kv1, _) ← mkTestKVar `κ₁
  let (kv2, _) ← mkTestKVar `κ₂
  let (kv3, _) ← mkTestKVar `κ₃
  let (acyclic, cyclic) := classifyKVars [kv1, kv2, kv3] [(kv1, kv2), (kv2, kv1)]
  let κ3acyclic := acyclic.any fun k => k.mvarId == kv3.mvarId
  if cyclic.length ≥ 1 && κ3acyclic then
    logInfo m!"PASS [cycle κ₁↔κ₂, standalone κ₃]"
  else
    logInfo m!"FAIL [cycle]"

-- Test: self-loop κ₁ → κ₁, standalone κ₂
#eval! show MetaM Unit from do
  let (kv1, _) ← mkTestKVar `κ₁
  let (kv2, _) ← mkTestKVar `κ₂
  let (acyclic, cyclic) := classifyKVars [kv1, kv2] [(kv1, kv1)]
  let κ1cyclic := cyclic.any fun k => k.mvarId == kv1.mvarId
  let κ2acyclic := acyclic.any fun k => k.mvarId == kv2.mvarId
  if κ1cyclic && κ2acyclic then
    logInfo m!"PASS [self-loop κ₁, standalone κ₂]"
  else
    logInfo m!"FAIL [self-loop]"

-- Test: 3-cycle κ₁→κ₂→κ₃→κ₁, only 1 cut needed
#eval! show MetaM Unit from do
  let (kv1, _) ← mkTestKVar `κ₁
  let (kv2, _) ← mkTestKVar `κ₂
  let (kv3, _) ← mkTestKVar `κ₃
  let (acyclic, cyclic) := classifyKVars [kv1, kv2, kv3]
    [(kv1, kv2), (kv2, kv3), (kv3, kv1)]
  if cyclic.length == 1 && acyclic.length == 2 then
    logInfo m!"PASS [3-cycle: 1 cut, 2 acyclic]"
  else
    logInfo m!"FAIL [3-cycle]: cyclic={repr cyclic.length}, acyclic={repr acyclic.length}"
