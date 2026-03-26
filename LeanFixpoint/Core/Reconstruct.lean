import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Subst
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion

/-!
# Proof Metadata Extraction

This module extracts the metadata from the fusion algorithm
(sol1, scope, elim*) needed to mechanically generate Lean4
proof terms for kernel-checked verification.

## Key Idea

After the solver computes solutions and we instantiate
`∃ κ := sol`, each conjunct falls into one of three cases.
The metadata tells the tactic generator exactly what to emit
for each case.

## Depth Annotations

Each `⇒` node in the constraint tree gets a depth `d`.
After `intro`, the Lean context has fvars where:
  - `fvar[2d]`   = the value variable from `∀ x:b. p ⇒ᵈ c`
  - `fvar[2d+1]` = the hypothesis variable

Depth annotations are preserved by `scope` since it only
selects sub-constraints without modifying structure.
-/

-- ══════════════════════════════════════════════
--  Section 1: Depth-Annotated Constraints
-- ══════════════════════════════════════════════

/-- A constraint node annotated with its depth (number of ancestor ⇒ nodes). -/
structure DepthConstraint where
  constraint : Constraint
  depth      : Nat
  deriving Repr

/-- Annotate every node in a constraint with its depth. -/
def Constraint.annotateDepth (c : Constraint) (d : Nat := 0) : List DepthConstraint :=
  match c with
  | .pred p       => [⟨.pred p, d⟩]
  | .conj c₁ c₂  => c₁.annotateDepth d ++ c₂.annotateDepth d
  | .imp x b p c' => [⟨.imp x b p c', d⟩] ++ c'.annotateDepth (d + 1)

/-- Collect the depths of all ⇒ binders on the path from root to each node. -/
def Constraint.binderDepths (c : Constraint) (d : Nat := 0) : List Nat :=
  match c with
  | .pred _       => []
  | .conj c₁ c₂  => c₁.binderDepths d ++ c₂.binderDepths d
  | .imp _ _ _ c' => [d] ++ c'.binderDepths (d + 1)

-- ══════════════════════════════════════════════
--  Section 2: Scope Depth Analysis
-- ══════════════════════════════════════════════

/--
  Scope analysis result for a single κ variable.

  - `outerDepths`: depths of ⇒ binders that `scope` strips away
    (those where κ ∉ pᵢ). These become the witnesses for head proofs.
  - `innerDepths`: depths of ⇒ binders inside `scope(κ,c)` after stripping.

  This is the key bridge between solver-level variables and Lean fvars.
-/
structure ScopeInfo where
  /-- Depths of binders stripped by scope (κ ∉ pᵢ) — witnesses come from here -/
  outerDepths : List Nat
  /-- Depths of binders inside the stripped scope — the "active" part -/
  innerDepths : List Nat
  /-- The scope sub-constraint itself -/
  scopedConstraint : Constraint
  /-- The stripped scope (after removing outer binders) -/
  strippedConstraint : Constraint
  /-- The sol1 predicate computed from the stripped scope -/
  solution : Pred
  deriving Repr

/-- Compute scope with depth tracking. -/
def Constraint.scopeWithDepth (κ : KVar) (c : Constraint) (d : Nat := 0)
    : (List Nat × Constraint) :=
  match c with
  | .conj c₁ c₂ =>
    let inC₁ := c₁.kvars.contains κ
    let inC₂ := c₂.kvars.contains κ
    if inC₁ && !inC₂ then c₁.scopeWithDepth κ d
    else if !inC₁ && inC₂ then c₂.scopeWithDepth κ d
    else ([], c)
  | .imp x b p c' =>
    if !(p.kvars.contains κ) then
      let (ds, remaining) := c'.scopeWithDepth κ (d + 1)
      ([d] ++ ds, .imp x b p remaining)
    else ([], c)
  | _ => ([], c)

/-- Compute stripScope with depth tracking.
    Returns (stripped depths, remaining constraint). -/
def stripScopeWithDepth (κ : KVar) (c : Constraint) (d : Nat := 0)
    : (List Nat × Constraint) :=
  match c with
  | .imp x b p c' =>
    if !p.kvars.contains κ then
      let (ds, remaining) := stripScopeWithDepth κ c' (d + 1)
      ([d] ++ ds, remaining)
    else ([], .imp x b p c')
  | _ => ([], c)

/-- Full scope analysis for a single κ variable. -/
def analyzeScopeFor (κ : KVar) (c : Constraint) : ScopeInfo :=
  let sc := c.scope κ
  let (outerDs, _) := c.scopeWithDepth κ
  let (stripDs, stripped) := stripScopeWithDepth κ sc
  let sol := stripped.sol1 κ
  { outerDepths := outerDs
    innerDepths := stripDs
    scopedConstraint := sc
    strippedConstraint := stripped
    solution := sol }

-- ══════════════════════════════════════════════
--  Section 3: Flat Clause Classification
-- ══════════════════════════════════════════════

/-- Classification of a flat clause for proof generation. -/
inductive ClauseKind where
  /-- κ in head, no κ in body: prove by providing scope witnesses -/
  | headOnly (headKVar : KVar) (scopeInfo : ScopeInfo)
  /-- κ in head, κ' in body: destructure body hyp, repackage for head -/
  | headBody (headKVar : KVar) (bodyKVar : KVar)
             (headScopeInfo : ScopeInfo) (bodyScopeInfo : ScopeInfo)
  /-- No κ in head: delegate to grind/omega -/
  | pureVC
  deriving Repr

/-- The source of witnesses for proof generation. -/
inductive WitnessSource where
  /-- Witnesses come from fvars at these absolute depths -/
  | fromScope (depths : List Nat)
  /-- Witnesses come from destructured hypothesis fvars -/
  | fromHyp
  deriving Repr

/-- Complete proof recipe for a single conjunct. -/
structure ConjunctProofInfo where
  /-- Which flat clause index this is -/
  index : Nat
  /-- Classification -/
  kind : ClauseKind
  /-- Depths of the clause's own ⇒ binders (for intro) -/
  clauseBinderDepths : List Nat
  /-- The solution predicate structure (for head clauses) -/
  headSolution : Option Pred
  /-- The body solution predicate structure (for headBody clauses) -/
  bodySolution : Option Pred
  /-- Whether a disjunction (Or.inl/Or.inr) is needed -/
  disjunctBranch : Option Bool  -- some true = left, some false = right
  deriving Repr

-- ══════════════════════════════════════════════
--  Section 4: Conjunct Classification Engine
-- ══════════════════════════════════════════════

/-- Get all depths of ⇒ binders in a flat constraint. -/
def FlatConstraint.binderDepthsFrom (fc : FlatConstraint) (startDepth : Nat := 0)
    : List Nat :=
  go fc.val startDepth
where
  go : Constraint → Nat → List Nat
    | .imp _ _ _ c', d => [d] ++ go c' (d + 1)
    | _, _             => []

/-- Classify a single flat clause given the scope info for all κ variables. -/
def classifyClause (fc : FlatConstraint) (scopeMap : List (KVar × ScopeInfo))
    (clauseIdx : Nat) (outerDepth : Nat) : ConjunctProofInfo :=
  let headKVars := fc.head.kvars
  let bodyKVars := (fc.body.map Pred.kvars).flatten
  let clauseDepths := fc.binderDepthsFrom outerDepth
  match headKVars with
  | [] =>
    { index := clauseIdx
      kind := .pureVC
      clauseBinderDepths := clauseDepths
      headSolution := none
      bodySolution := none
      disjunctBranch := none }
  | headK :: _ =>
    let headSI := match scopeMap.find? (fun (k, _) => k == headK) with
      | some (_, si) => si
      | none => analyzeScopeFor headK (.pred .tru)
    let bodyKFiltered := bodyKVars.filter (fun k => scopeMap.any (fun (k', _) => k == k'))
    match bodyKFiltered with
    | [] =>
      { index := clauseIdx
        kind := .headOnly headK headSI
        clauseBinderDepths := clauseDepths
        headSolution := some headSI.solution
        bodySolution := none
        disjunctBranch := none }
    | bodyK :: _ =>
      let bodySI := match scopeMap.find? (fun (k, _) => k == bodyK) with
        | some (_, si) => si
        | none => analyzeScopeFor bodyK (.pred .tru)
      { index := clauseIdx
        kind := .headBody headK bodyK headSI bodySI
        clauseBinderDepths := clauseDepths
        headSolution := some headSI.solution
        bodySolution := some bodySI.solution
        disjunctBranch := none }

-- ══════════════════════════════════════════════
--  Section 5: Disjunction Branch Detection
-- ══════════════════════════════════════════════

/--
  When sol1 traverses `c₁ ∧ c₂`, it produces `sol1(κ,c₁) ∨ sol1(κ,c₂)`.
  For a head clause from the left branch, we need `Or.inl`;
  for the right branch, `Or.inr`.
-/
def detectDisjunctBranch (κ : KVar) (originalConj : Constraint)
    (fc : FlatConstraint) : Option Bool :=
  match originalConj with
  | .conj c₁ c₂ =>
    let headHasK := fc.head.kvars.contains κ
    if !headHasK then none
    else
      let flat₁ := c₁.flat
      let flat₂ := c₂.flat
      let inC₁ := flat₁.any (fun fc' => fc'.val.kvars == fc.val.kvars)
      let inC₂ := flat₂.any (fun fc' => fc'.val.kvars == fc.val.kvars)
        if inC₁ && !inC₂
        then some Bool.true
        else if !inC₁ && inC₂ then some Bool.false
        else none
  | _ => none

-- ══════════════════════════════════════════════
--  Section 6: Solution Structure Walker
-- ══════════════════════════════════════════════

/--
  The proof structure mirrors `sol1`'s output.
  This ADT describes the tactic steps needed.
-/
inductive ProofStep where
  | existsFromScope (depth : Nat)
  | existsFromHyp (hypIdx : Nat)
  | constr
  | exactFromScope (depth : Nat)
  | exactFromHyp (hypIdx : Nat)
  | inl
  | inr
  | introNames (names : List String)
  | obtainFrom (pattern : String) (hypName : String)
  | grindStep
  | omegaStep
  deriving Repr

/--
  Walk the solution predicate and emit proof steps.
  `source` determines where witnesses come from.
-/
def emitProofSteps (sol : Pred) (source : WitnessSource)
    (depthIdx : Nat := 0) : List ProofStep :=
  match sol with
  | .exist _ _ (.conj _p rest) =>
    let (existStep, exactStep) := match source with
      | .fromScope depths =>
        let d := depths.getD depthIdx 0
        (ProofStep.existsFromScope d, ProofStep.exactFromScope d)
      | .fromHyp =>
        (ProofStep.existsFromHyp (2 * depthIdx), ProofStep.exactFromHyp (2 * depthIdx + 1))
    [existStep, .constr, exactStep] ++ emitProofSteps rest source (depthIdx + 1)

  | .exist _ _ _inner =>
    let existStep := match source with
      | .fromScope depths =>
        let d := depths.getD depthIdx 0
        ProofStep.existsFromScope d
      | .fromHyp =>
        ProofStep.existsFromHyp (2 * depthIdx)
    [existStep]

  | .disj left _right =>
    [.inl] ++ emitProofSteps left source depthIdx

  | .conj p₁ p₂ =>
    [.constr] ++ emitProofSteps p₁ source depthIdx
    ++ emitProofSteps p₂ source depthIdx

  | .rexpr _ => []
  | .tru     => []
  | .fls     => [.grindStep]
  | .kapp _ _ => [.grindStep]

-- ══════════════════════════════════════════════
--  Section 7: Full Proof Plan
-- ══════════════════════════════════════════════

/-- Complete proof plan for the entire constraint. -/
structure ProofPlan where
  solutions : List (KVar × Pred)
  outerBinderDepths : List Nat
  numOuterIntros : Nat
  numConjuncts : Nat
  conjuncts : List ConjunctProofInfo
  deriving Repr

/-- Helper: zip a list with indices. -/
private def withIndex (xs : List α) : List (Nat × α) :=
  go xs 0
where
  go : List α → Nat → List (Nat × α)
    | [], _ => []
    | x :: rest, i => (i, x) :: go rest (i + 1)

/--
  Build a complete proof plan for a constraint with given κ variables.
  This is the main entry point for the tactic.
-/
def buildProofPlan (kvars : List KVar) (c : Constraint) : ProofPlan :=
  let scopeMap := kvars.map (fun κ => (κ, analyzeScopeFor κ c))
  let solutions := scopeMap.map (fun (κ, si) => (κ, si.solution))
  let outerDepths := match scopeMap.head? with
    | some (_, si) => si.outerDepths
    | none => []
  let flatClauses := c.flat
  let conjuncts := (withIndex flatClauses).map (fun (i, fc) =>
    classifyClause fc scopeMap i outerDepths.length)
  { solutions := solutions
    outerBinderDepths := outerDepths
    numOuterIntros := outerDepths.length * 2
    numConjuncts := flatClauses.length
    conjuncts := conjuncts }

-- ══════════════════════════════════════════════
--  Section 8: Pretty Printing for Debugging
-- ══════════════════════════════════════════════

def ProofStep.toString : ProofStep → String
  | .existsFromScope d => s!"exists fvar[{2*d}]"
  | .existsFromHyp i   => s!"exists hyp[{i}]"
  | .constr             => "constructor"
  | .exactFromScope d   => s!"· exact fvar[{2*d+1}]"
  | .exactFromHyp i     => s!"· exact hyp[{i}]"
  | .inl                => "left"
  | .inr                => "right"
  | .introNames names   => s!"intro {" ".intercalate names}"
  | .obtainFrom pat hyp => s!"obtain {pat} := {hyp}"
  | .grindStep          => "grind"
  | .omegaStep          => "omega"

instance : ToString ProofStep := ⟨ProofStep.toString⟩

def ClauseKind.toString : ClauseKind → String
  | .headOnly k si =>
    s!"HEAD-ONLY κ={k.name}, outerDepths={si.outerDepths}, innerDepths={si.innerDepths}"
  | .headBody hk bk hsi _bsi =>
    s!"HEAD-BODY head={hk.name} body={bk.name}, outerDepths={hsi.outerDepths}"
  | .pureVC => "PURE-VC (grind)"

instance : ToString ClauseKind := ⟨ClauseKind.toString⟩

def ConjunctProofInfo.toString (info : ConjunctProofInfo) : String :=
  let kindStr := info.kind.toString
  let solStr := match info.headSolution with
    | some sol => s!"\n    headSol = {sol}"
    | none => ""
  let bodySolStr := match info.bodySolution with
    | some sol => s!"\n    bodySol = {sol}"
    | none => ""
  let branchStr := match info.disjunctBranch with
    | some b => if b then "\n    branch = LEFT" else "\n    branch = RIGHT"
    | none => ""
  s!"  Conjunct[{info.index}]: {kindStr}{solStr}{bodySolStr}{branchStr}\n    clauseDepths = {info.clauseBinderDepths}"

instance : ToString ConjunctProofInfo := ⟨ConjunctProofInfo.toString⟩

def ProofPlan.toString (plan : ProofPlan) : String :=
  let solStrs := plan.solutions.map (fun (k, sol) =>
    s!"  {k.name} ↦ {sol}")
  let conjStrs := plan.conjuncts.map (fun ci => ci.toString)
  s!"ProofPlan:\n  outerDepths = {plan.outerBinderDepths}\n  numOuterIntros = {plan.numOuterIntros}\n  numConjuncts = {plan.numConjuncts}\n\nSolutions:\n{"\n".intercalate solStrs}\n\nConjuncts:\n{"\n".intercalate conjStrs}"

instance : ToString ProofPlan := ⟨ProofPlan.toString⟩

-- ══════════════════════════════════════════════
--  Section 9: Tactic Script Generation (pure)
-- ══════════════════════════════════════════════

/-- Build tactic lines for a single conjunct. -/
private def scriptForConjunct (info : ConjunctProofInfo) : String :=
  let header := s!"  -- Conjunct {info.index}\n"
  match info.kind with
  | .pureVC =>
    header ++ "  · grind\n"
  | .headOnly _κ si =>
    let introNames := (List.range (info.clauseBinderDepths.length * 2)).map (fun i =>
      if i % 2 == 0 then s!"v{i/2}" else s!"hv{i/2}")
    let introLine :=
      if introNames.length > 0
      then s!"  · intro {" ".intercalate introNames}\n"
      else ""
    let steps := emitProofSteps si.solution (.fromScope si.outerDepths)
    let stepLines := steps.map (fun step => s!"    {step}\n")
    header ++ introLine ++ String.join stepLines
  | .headBody _hκ _bκ hsi _bsi =>
    let introNames := (List.range (info.clauseBinderDepths.length * 2)).map (fun i =>
      if i % 2 == 0 then s!"v{i/2}" else s!"hv{i/2}")
    let introLine :=
      if introNames.length > 0
      then s!"  · intro {" ".intercalate introNames}\n"
      else ""
    let steps := emitProofSteps hsi.solution .fromHyp
    let stepLines := steps.map (fun step => s!"    {step}\n")
    let destructNote := match info.bodySolution with
      | some _ => s!"    -- (destructure body hyp, repackage)\n"
      | none => ""
    header ++ introLine ++ String.join stepLines ++ destructNote

/--
  Generate a textual tactic script from a proof plan.
  This is a debugging aid; the real tactic will emit `Syntax` directly.
-/
def generateTacticScript (plan : ProofPlan) : String :=
  let existLines := plan.solutions.map (fun (_, sol) => s!"  exists {sol}\n")
  let dsimpLine := "  dsimp only\n"
  let introLine :=
    if plan.numOuterIntros > 0 then
      let names := (List.range plan.numOuterIntros).map (fun i =>
        if i % 2 == 0 then s!"x{i/2}" else s!"h{i/2}")
      s!"  intro {" ".intercalate names}\n"
    else ""
  let splitLine :=
    if plan.numConjuncts > 1 then
      let holes := (List.range plan.numConjuncts).map (fun _ => "?_")
      s!"  refine ⟨{", ".intercalate holes}⟩\n"
    else ""
  let conjunctLines := plan.conjuncts.map scriptForConjunct
  String.join existLines ++ dsimpLine ++ introLine ++ splitLine ++ String.join conjunctLines

-- ══════════════════════════════════════════════
--  Section 10: Test on Examples
-- ══════════════════════════════════════════════

section Tests

def kappa1_test : KVar := { name := `κ₁, params := [`z] }

def ex1TestConstraint : Constraint :=
  c{
    ∀ x : int . 0 ≤ x ⇒
      [∀ ν : int . ν == x - 1 ⇒ kappa1_test(ν)]
    ∧ [∀ y : int . kappa1_test(y) ⇒
        ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν]
  }

#eval do
  let plan := buildProofPlan [kappa1_test] ex1TestConstraint
  IO.println plan.toString
  IO.println "\n--- Generated Tactic Script ---"
  IO.println (generateTacticScript plan)

def kx_test : KVar := { name := `κx, params := [`z] }
def ky_test : KVar := { name := `κy, params := [`z] }

def ex2TestConstraint : Constraint :=
  c{
    ∀ x : int . 0 ≤ x ⇒
    ∀ n : int . n == x - 1 ⇒
    ∀ p : int . p == x + 1 ⇒
      [∀ ν : int . ν == n ⇒ kx_test(ν)]
    ∧ [∀ ν : int . ν == p ⇒ ky_test(ν)]
    ∧ [∀ ν : int . kx_test(ν) ⇒ ky_test(ν)]
    ∧ [∀ y : int . ky_test(y) ⇒
        ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν]
  }

#eval do
  let plan := buildProofPlan [kx_test, ky_test] ex2TestConstraint
  IO.println plan.toString
  IO.println "\n--- Generated Tactic Script ---"
  IO.println (generateTacticScript plan)

def ka_test : KVar := { name := `κa, params := [`z] }
def kb_test : KVar := { name := `κb, params := [`z] }
def kc_test : KVar := { name := `κc, params := [`z] }

def ex3TestConstraint : Constraint :=
  c{
    [∀ a : int . ka_test(a) ⇒ ∀ ν : int . ν == a - 1 ⇒ kb_test(ν)]
  ∧ [∀ b : int . kb_test(b) ⇒ ∀ ν : int . ν == b + 1 ⇒ kc_test(ν)]
  ∧ [∀ ν : int . 0 ≤ ν ⇒ ka_test(ν)]
  ∧ [∀ ν : int . kc_test(ν) ⇒ 0 ≤ ν]
  }

#eval do
  let plan := buildProofPlan [ka_test, kb_test, kc_test] ex3TestConstraint
  IO.println plan.toString
  IO.println "\n--- Generated Tactic Script ---"
  IO.println (generateTacticScript plan)

end Tests
