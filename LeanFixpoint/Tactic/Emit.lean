import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Subst
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Fusion

open Lean
/-!
# Emit: ProofPlan → TacticM

This module implements the recursive proof generation that walks
`sol1`'s Pred output and emits tactic steps to close each conjunct.

## Architecture

After `exists sol₁; ...; exists solₙ; dsimp only; intro ...; refine ⟨...⟩`,
each conjunct goal has a specific shape dictated by the solutions.
This module closes each goal mechanically.

## Key Invariant

`sol1` traverses ∀-binders left-to-right, producing ∃-nodes in the
same order. After `intro`, fvars appear in the same order.
Therefore the i-th ∃ node in sol1 corresponds to fvar index i.
-/

-- ══════════════════════════════════════════════
--  Section 1: Proof Trace (testable without Lean.Elab)
-- ══════════════════════════════════════════════

/--
  A proof trace is a sequence of tactic-like actions that can be:
  1. Pretty-printed for debugging
  2. Replayed in TacticM for actual proof generation

  This is the "intermediate representation" between the solver
  metadata and the actual tactic calls.
-/
inductive ProofTrace where
  | existsWitness (source : String) (idx : Nat)
  | constructorSplit
  | exactHyp (source : String) (idx : Nat)
  | introBindersT (count : Nat)
  | obtainDestruct (solShape : String) (hypName : String)
  | leftBranch
  | rightBranch
  | grindClose
  | focusLeft (inner : List ProofTrace)
  | focusRight (inner : List ProofTrace)
  deriving Repr

def ProofTrace.prettyPrint (indent : Nat := 0) : ProofTrace → String
  | .existsWitness src idx =>
    " ".replicate indent ++ s!"exists {src}[{idx}]"
  | .constructorSplit =>
    " ".replicate indent ++ "constructor"
  | .exactHyp src idx =>
    " ".replicate indent ++ s!"exact {src}[{idx}]"
  | .introBindersT n =>
    " ".replicate indent ++ s!"intro ({n} binders)"
  | .obtainDestruct shape hyp =>
    " ".replicate indent ++ s!"obtain ⟨{shape}⟩ := {hyp}"
  | .leftBranch =>
    " ".replicate indent ++ "left"
  | .rightBranch =>
    " ".replicate indent ++ "right"
  | .grindClose =>
    " ".replicate indent ++ "grind"
  | .focusLeft inner =>
    let hdr := " ".replicate indent ++ "· -- left\n"
    let body := inner.map (ProofTrace.prettyPrint (indent + 2))
    hdr ++ "\n".intercalate body
  | .focusRight inner =>
    let hdr := " ".replicate indent ++ "· -- right\n"
    let body := inner.map (ProofTrace.prettyPrint (indent + 2))
    hdr ++ "\n".intercalate body

instance : ToString ProofTrace where
  toString t := t.prettyPrint

-- ══════════════════════════════════════════════
--  Section 2: Witness/Hypothesis Source Tracking
-- ══════════════════════════════════════════════

/--
  Tracks where each ∃-witness and ∧-hypothesis comes from.

  After intro, the proof context has:
    outerFVars:  [x₀, h₀, x₁, h₁, ...]  (from shared outer scope)
    clauseFVars: [v₀, hv₀, v₁, hv₁, ...] (from this clause's own binders)

  We flatten these into two parallel arrays:
    witnesses:  [x₀, x₁, ..., v₀, v₁, ...]   (value fvars only)
    hypotheses: [h₀, h₁, ..., hv₀, hv₁, ...]  (hyp fvars only)

  The i-th ∃ node in sol1 uses witnesses[i] and hypotheses[i].
-/
structure FVarSources where
  /-- Value fvars: outerScope values ++ clauseLocal values -/
  witnessCount : Nat
  /-- Hyp fvars: outerScope hyps ++ clauseLocal hyps -/
  hypCount : Nat
  /-- Fvars from destructured body hyp (headBody only) -/
  destrCount : Nat
  deriving Repr

-- ══════════════════════════════════════════════
--  Section 3: Core Emit — Walk sol1's Pred Tree
-- ══════════════════════════════════════════════

/--
  Emit proof trace for providing an existential witness and proving
  the associated hypothesis.

  This is the core recursive function. It walks the Pred tree from sol1
  and produces a ProofTrace for each node.

  Returns: (trace, next witness index, next destructor index)
-/
partial def emitExistProofTrace (sol : Pred) (wIdx : Nat) (dIdx : Nat)
    (isBodyNested : Bool := false)
    : (List ProofTrace × Nat × Nat) :=
  match sol with
  | .exist _ _ (.conj hypPred rest) =>
    -- Pattern: ∃ x:b. HYP ∧ REST
    let srcTag := if isBodyNested then "destr" else "wit"
    let existTrace := ProofTrace.existsWitness srcTag wIdx
    let constrTrace := ProofTrace.constructorSplit

    -- Prove the hypothesis (left of ∧)
    let (hypTraces, wIdx', dIdx') := emitHypProofTrace hypPred wIdx dIdx isBodyNested

    -- Continue with rest (right of ∧)
    let (restTraces, wIdx'', dIdx'') := emitExistProofTrace rest (wIdx + 1) dIdx' isBodyNested

    let allTraces := [existTrace, constrTrace]
      ++ [ProofTrace.focusLeft hypTraces]
      ++ [ProofTrace.focusRight restTraces]
    (allTraces, wIdx'', dIdx'')

  | .exist _ _ _leaf =>
    -- Pattern: ∃ x:b. LEAF (no conjunction, leaf closed by unification)
    let srcTag := if isBodyNested then "destr" else "wit"
    ([ProofTrace.existsWitness srcTag wIdx], wIdx + 1, dIdx)

  | .disj left _right =>
    -- From c₁ ∧ c₂ in stripped scope: sol1 = sol1(c₁) ∨ sol1(c₂)
    -- Branch selection handled by caller
    -- Default: emit left branch (caller wraps with left/right)
    emitExistProofTrace left wIdx dIdx isBodyNested

  | .rexpr _ => ([], wIdx, dIdx)  -- leaf: closed by unification
  | .tru     => ([], wIdx, dIdx)
  | _        => ([ProofTrace.grindClose], wIdx, dIdx)

/--
  Emit proof trace for proving a hypothesis (the ∧-left child).

  Two cases:
  1. Simple predicate (rexpr): use the corresponding hyp fvar or grind
  2. Nested ∃/∧ (body sol embedded in head sol): re-wrap destructured pieces
-/
partial def emitHypProofTrace (hyp : Pred) (wIdx : Nat) (dIdx : Nat)
    (isBodyNested : Bool)
    : (List ProofTrace × Nat × Nat) :=
  match hyp with
  | .rexpr _ =>
    -- Simple refinement predicate → exact the hyp fvar or grind
    if isBodyNested then
      ([ProofTrace.exactHyp "destr" dIdx], wIdx, dIdx + 1)
    else
      ([ProofTrace.exactHyp "hyp" wIdx], wIdx, dIdx)

  | .exist _ _ (.conj inner rest) =>
    -- Nested solution (body sol embedded in head sol)
    -- Witnesses come from destructured body hyp
    let existTrace := ProofTrace.existsWitness "destr" dIdx
    let constrTrace := ProofTrace.constructorSplit
    let (innerTraces, _, dIdx') := emitHypProofTrace inner wIdx (dIdx + 1) true
    let (restTraces, _, dIdx'') := emitHypProofTrace rest wIdx dIdx' true
    let allTraces := [existTrace, constrTrace]
      ++ [ProofTrace.focusLeft innerTraces]
      ++ [ProofTrace.focusRight restTraces]
    (allTraces, wIdx, dIdx'')

  | .exist _ _ _leaf =>
    ([ProofTrace.existsWitness "destr" dIdx], wIdx, dIdx + 1)

  | .conj p₁ p₂ =>
    let (t1, w1, d1) := emitHypProofTrace p₁ wIdx dIdx isBodyNested
    let (t2, w2, d2) := emitHypProofTrace p₂ w1 d1 isBodyNested
    ([ProofTrace.constructorSplit] ++ [ProofTrace.focusLeft t1] ++ [ProofTrace.focusRight t2], w2, d2)

  | .tru => ([], wIdx, dIdx)
  | _    => ([ProofTrace.grindClose], wIdx, dIdx)

-- ══════════════════════════════════════════════
--  Section 4: Full Conjunct Trace Generation
-- ══════════════════════════════════════════════

/-- Generate the complete proof trace for a headOnly conjunct. -/
def emitHeadOnlyTrace (sol : Pred) (numClauseBinders : Nat)
    (numOuterWitnesses : Nat) : List ProofTrace :=
  let introTrace :=
    if numClauseBinders > 0
    then [ProofTrace.introBindersT numClauseBinders]
    else []
  -- Witnesses: outer scope first, then clause-local
  -- wIdx 0..numOuter-1 = outer, numOuter.. = clause-local
  let (proofTraces, _, _) := emitExistProofTrace sol 0 0 false
  introTrace ++ proofTraces

/-- Generate the complete proof trace for a headBody conjunct. -/
def emitHeadBodyTrace (headSol : Pred) (bodySol : Pred)
    (numClauseBinders : Nat) (bodyHypBinderIdx : Nat)
    (branch : Option Bool) : List ProofTrace :=
  let introTrace :=
    if numClauseBinders > 0
    then [ProofTrace.introBindersT numClauseBinders]
    else []
  -- Destructure the body hypothesis
  let destrTrace := [ProofTrace.obtainDestruct (toString bodySol) s!"hyp[{bodyHypBinderIdx}]"]
  -- Branch if needed
  let branchTrace := match branch with
    | some isLeft => if isLeft then [ProofTrace.leftBranch] else [ProofTrace.rightBranch]
    | Option.none => []
  -- Build head proof; the ∧-left children that match body sol
  -- use destructured pieces (isBodyNested will be set appropriately)
  let (proofTraces, _, _) := emitExistProofTrace headSol 0 0 false
  introTrace ++ destrTrace ++ branchTrace ++ proofTraces

/-- Generate proof trace for a pureVC conjunct. -/
def emitPureVCTrace : List ProofTrace :=
  [ProofTrace.grindClose]

-- ══════════════════════════════════════════════
--  Section 5: Destructure Pattern Generation
-- ══════════════════════════════════════════════

/--
  Generate the obtain pattern string for destructuring a body hypothesis.

  sol_κa = ∃ ν. 0≤ν ∧ z=ν
    → "ν₀, hν₀, ha_eq"

  sol_κb = ∃ a. (∃ ν. 0≤ν ∧ a=ν) ∧ ∃ ν. ν=a-1 ∧ b=ν
    → "a, ⟨ν₀, hν₀, ha_eq⟩, ν₁, hν₁, hb_eq"
-/
partial def generateObtainPattern (sol : Pred) (prefix_ : String) (idx : Nat := 0)
    : (String × Nat) :=
  match sol with
  | .exist _ _ (.conj hypPred rest) =>
    let valName := s!"{prefix_}{idx}"
    let (hypPat, idx') := generateHypPattern hypPred prefix_ idx
    let (restPat, idx'') := generateObtainPattern rest prefix_ (idx' + 1)
    (s!"{valName}, {hypPat}, {restPat}", idx'')

  | .exist _ _ _leaf =>
    let valName := s!"{prefix_}{idx}"
    (s!"{valName}, h{prefix_}{idx}", idx + 1)

  | _ => (s!"h{prefix_}{idx}", idx + 1)

partial def generateHypPattern (hyp : Pred) (prefix_ : String) (idx : Nat)
    : (String × Nat) :=
  match hyp with
  | .rexpr _ => (s!"h{prefix_}{idx}", idx)
  | .exist _ _ (.conj inner rest) =>
    let valName := s!"{prefix_}_{idx}"
    let (innerPat, idx') := generateHypPattern inner prefix_ idx
    let (restPat, idx'') := generateHypPattern rest prefix_ (idx' + 1)
    (s!"⟨{valName}, {innerPat}, {restPat}⟩", idx'')
  | .exist _ _ _leaf =>
    (s!"⟨{prefix_}_{idx}, h{prefix_}_{idx}⟩", idx + 1)
  | _ => (s!"h{prefix_}{idx}", idx)

-- ══════════════════════════════════════════════
--  Section 6: Count Destructured Pieces
-- ══════════════════════════════════════════════

/-- Count how many fvars destructuring a body solution produces. -/
partial def countDestructuredFVars (sol : Pred) : Nat :=
  match sol with
  | .exist _ _ (.conj hypPred rest) =>
    1 + countHypFVars hypPred + countDestructuredFVars rest
  | .exist _ _ _leaf => 2  -- value + proof
  | _ => 1

partial def countHypFVars (hyp : Pred) : Nat :=
  match hyp with
  | .rexpr _ => 1
  | .exist _ _ (.conj inner rest) =>
    1 + countHypFVars inner + countHypFVars rest
  | .exist _ _ _ => 2
  | _ => 1

-- ══════════════════════════════════════════════
--  Section 7: Trace → Tactic Script (for testing)
-- ══════════════════════════════════════════════

/-- Convert a trace to a human-readable tactic script. -/
def traceToScript (traces : List ProofTrace) (indent : Nat := 4) : String :=
  let lines := traces.map (fun t => t.prettyPrint indent)
  "\n".intercalate lines

-- ══════════════════════════════════════════════
--  Section 8: Integration Test
-- ══════════════════════════════════════════════

section EmitTests

-- Test: ex1 clause A (headOnly)
-- sol_κ = ∃ x. 0≤x ∧ ∃ ν. ν=x-1 ∧ z=ν
-- 2 outer scope witnesses (x, ν from clause), 1 clause binder pair (ν, hν)
def testSol1 : Pred :=
  .exist `x .int (.conj (.rexpr (.mkLeq (.lit 0) (.var `x)))
    (.exist `ν .int (.conj (.rexpr (.mkEq (.var `ν) (.mkSub (.var `x) (.lit 1))))
      (.rexpr (.mkEq (.var `z) (.var `ν))))))

#eval do
  IO.println "=== Ex1 Clause A (headOnly) ==="
  let traces := emitHeadOnlyTrace testSol1 2 1
  IO.println (traceToScript traces)

-- Test: ex3 clause 2 (headOnly, κa)
-- sol_κa = ∃ ν. 0≤ν ∧ z=ν
-- 0 outer scope witnesses, 1 clause binder pair (ν, hν)
def testSolKa : Pred :=
  .exist `ν .int (.conj (.rexpr (.mkLeq (.lit 0) (.var `ν)))
    (.rexpr (.mkEq (.var `z) (.var `ν))))

#eval do
  IO.println "=== Ex3 Clause 2 (headOnly, κa) ==="
  let traces := emitHeadOnlyTrace testSolKa 2 0
  IO.println (traceToScript traces)

-- Test: ex3 clause 0 (headBody, head=κb, body=κa)
-- sol_κb = ∃ a. (∃ ν. 0≤ν ∧ a=ν) ∧ ∃ ν. ν=a-1 ∧ z=ν
-- body sol = sol_κa
def testSolKb : Pred :=
  .exist `a .int (.conj
    (.exist `ν .int (.conj (.rexpr (.mkLeq (.lit 0) (.var `ν)))
      (.rexpr (.mkEq (.var `a) (.var `ν)))))
    (.exist `ν .int (.conj (.rexpr (.mkEq (.var `ν) (.mkSub (.var `a) (.lit 1))))
      (.rexpr (.mkEq (.var `z) (.var `ν))))))

#eval do
  IO.println "=== Ex3 Clause 0 (headBody, head=κb, body=κa) ==="
  let traces := emitHeadBodyTrace testSolKb testSolKa 4 1 Option.none
  IO.println (traceToScript traces)

-- Test: obtain pattern generation
#eval do
  IO.println "=== Obtain pattern for sol_κa ==="
  let (pat, _) := generateObtainPattern testSolKa "v" 0
  IO.println s!"obtain ⟨{pat}⟩ := ha"

#eval do
  IO.println "=== Obtain pattern for sol_κb ==="
  let (pat, _) := generateObtainPattern testSolKb "v" 0
  IO.println s!"obtain ⟨{pat}⟩ := hb"

-- Test: count destructured fvars
#eval do
  IO.println s!"sol_κa destructs into {countDestructuredFVars testSolKa} fvars"
  IO.println s!"sol_κb destructs into {countDestructuredFVars testSolKb} fvars"

end EmitTests
