import LeanFixpoint

open Lean Meta Elab Term

-- Dedicated qualifiers for testing. Separate from FibFibFast's q_gt_one etc.
-- so the environment tagset stays predictable.
@[qualif] private def _wt_gt_one  (v : Int)    : Prop := v > 1
@[qualif] private def _wt_le      (a b : Int)  : Prop := a ≤ b
@[qualif] private def _wt_eq      (a b : Int)  : Prop := a = b
@[qualif] private def _wt_lt_zero (v : Int)    : Prop := v < 0

/-- Runs `specializeClauseForHead` on every flat clause of `stmt`'s body
    (which must be of the form `∃ κ : …, body`) and prints before/after.

    For simplicity we assume ONE κ; `assignment` is optional (default `[]`). -/
private def runSpec
    (desc       : String)
    (stmt       : Expr)
    (q          : Expr)
    (qSlots     : List Nat)
    (assignment : List (KVar × Expr) := [])
    : TermElabM Unit := do
  IO.println s!"\n===== {desc} ====="
  let goalMVar ← mkFreshExprMVar (some stmt)
  let (kvarMap, _kvarsRev, bodyGoalId) ← peelExistentialsAndIntro goalMVar.mvarId!
  let body ← bodyGoalId.getType
  let kctx : KContext := { kvars := kvarMap }
  let kvars : List KVar := kvarMap.values
  match kvars with
  | [headKVar] =>
    IO.println s!"  κ = {headKVar.name}, arity = {headKVar.params.length}"
    let clauses ← (exprFlat body).run kctx
    let mut i := 0
    for fc in clauses do
      IO.println s!"  clause {i}: {← ppExpr fc}"
      try
        let res ← (specializeClauseForHead headKVar q qSlots assignment fc).run kctx
        IO.println s!"          → {← ppExpr res}"
      catch e =>
        IO.println s!"          ! error: {← e.toMessageData.toString}"
      i := i + 1
  | _ =>
    IO.println s!"  (expected exactly one κ, got {kvars.length})"

run_cmd Lean.Elab.Command.liftTermElabM do
  let qGt ← mkConstWithLevelParams ``_wt_gt_one
  let qLe ← mkConstWithLevelParams ``_wt_le

  -- A: simplest — 1-arg κ, single clause with head-only κ-app
  let sA ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, κ x)) none
  runSpec "A  1-arg κ, head-only, q_gt_one at [0]" sA qGt [0]
  -- Expect: ∀ x : Int, x > 1

  -- B: 1-arg κ, hypothesis (non-κ) + head
  let sB ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, 0 ≤ x → κ x)) none
  runSpec "B  1-arg κ, (0 ≤ x) → κ x,   q_gt_one at [0]" sB qGt [0]
  -- Expect: ∀ x : Int, 0 ≤ x → x > 1

  -- C: 2-arg κ, q_le at [0, 1] — identity slot mapping
  let sC ← elabTerm (← `(∃ κ : Int → Int → Prop, ∀ a b : Int, κ a b)) none
  runSpec "C  2-arg κ, q_le at [0, 1]" sC qLe [0, 1]
  -- Expect: ∀ a b : Int, a ≤ b

  -- D: same clause, reversed slot mapping (b ≤ a) — tests slot perm
  runSpec "D  2-arg κ, q_le at [1, 0]  (slot reversal)" sC qLe [1, 0]
  -- Expect: ∀ a b : Int, b ≤ a

  -- E: 4-arg κ, 1-ary qualifier bound to middle slot — ghost args [0,1,3]
  let sE ← elabTerm (← `(∃ κ : Int → Int → Int → Int → Prop,
                           ∀ a b c d : Int, κ a b c d)) none
  runSpec "E  4-arg κ, q_gt_one at [2]  (ghost args 0,1,3)" sE qGt [2]
  -- Expect: ∀ a b c d : Int, c > 1

  -- F: 1-arg κ, chained foralls — verifies scoping preservation
  let sF ← elabTerm (← `(∃ κ : Int → Prop,
                           ∀ x : Int, 0 ≤ x → ∀ y : Int, y = x + 1 → κ y)) none
  runSpec "F  1-arg κ, chained ∀ and hyps, q_gt_one at [0]" sF qGt [0]
  -- Expect: ∀ x, 0 ≤ x → ∀ y, y = x + 1 → y > 1

  -- G: 2-arg κ, clause with TWO head κ-apps in conjunction
  let sG ← elabTerm (← `(∃ κ : Int → Int → Prop,
                           ∀ a b : Int, κ a b ∧ κ b a)) none
  runSpec "G  2-arg κ, conj (κ a b ∧ κ b a), q_le at [0, 1]" sG qLe [0, 1]
  -- exprFlat should split this into 2 clauses:
  --   clause 0: ∀ a b, κ a b  →  ∀ a b, a ≤ b
  --   clause 1: ∀ a b, κ b a  →  ∀ a b, b ≤ a
  -- (remember: the head args of clause 1 are (b, a), so with qSlots=[0,1]
  --  we project [b, a] and β-apply q_le → b ≤ a. Slot reversal happens
  --  *automatically* because the κ-app in the clause uses (b, a), not (a, b).)

  -- H: FibFibFast-shaped seed clause — 4-arg κ, constants as head args
  let sH ← elabTerm (← `(∃ κ : Int → Int → Int → Int → Prop,
                           ∀ n : Int, n ≥ 0 → κ 2 1 2 n)) none
  runSpec "H  FibFibFast seed shape, q_le at [0, 3]" sH qLe [0, 3]
  -- Expect: ∀ n : Int, n ≥ 0 → 2 ≤ n
  -- (args = #[2, 1, 2, n]; qSlots=[0,3] picks 2 and n; q_le 2 n = 2 ≤ n.)

run_cmd Lean.Elab.Command.liftTermElabM do
  let qGt ← mkConstWithLevelParams ``_wt_gt_one
  -- q_le not used here — we pick 1-arg κ's so only q_gt_one is slot-compatible

  ----------------------------------------------------------------------
  -- Weaken-A: candidate SHOULD be dropped.
  --
  -- Constraint: ∃ κ : Int → Prop, ∀ x : Int, 0 ≤ x → κ x
  -- Candidates: [(q_gt_one, [0])]    -- i.e. claim is "κ x means x > 1"
  -- VC: 0 ≤ x → x > 1                -- FALSE (x could be 0)
  -- checkExprVC rejects → weakenOnce drops the candidate → survivors: 0
  ----------------------------------------------------------------------
  let stmt1 ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, 0 ≤ x → κ x)) none
  let goalMVar1 ← mkFreshExprMVar (some stmt1)
  let (kvarMap, _kvarsRev, bodyGoalId) ← peelExistentialsAndIntro goalMVar1.mvarId!
  let body ← bodyGoalId.getType
  let kctx : KContext := { kvars := kvarMap }
  match kvarMap.values with
  | [κ] =>
    let initial : List (KVar × List (Expr × List Nat)) := [(κ, [(qGt, [0])])]
    let flat ← (exprFlat body).run kctx
    IO.println s!"\nWeaken-A (should DROP):"
    IO.println s!"  input:     1 candidate"
    let after ← weakenOnce kctx flat initial
    for (_, cands) in after do
      IO.println s!"  survivors: {cands.length}   (expect 0)"
  | _ => IO.println "unexpected κ count"

  ----------------------------------------------------------------------
  -- Weaken-B: candidate SHOULD be kept.
  --
  -- Constraint: ∃ κ : Int → Prop, ∀ x : Int, x = 2 → κ x
  -- Candidates: [(q_gt_one, [0])]
  -- VC: x = 2 → x > 1                -- TRUE
  -- checkExprVC accepts → weakenOnce keeps the candidate → survivors: 1
  ----------------------------------------------------------------------
  let stmt2 ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, x = 2 → κ x)) none
  let goalMVar2 ← mkFreshExprMVar (some stmt2)
  let (kvarMap, _kvarsRev, bodyGoalId) ← peelExistentialsAndIntro goalMVar2.mvarId!
  let body ← bodyGoalId.getType
  let kctx : KContext := { kvars := kvarMap }
  match kvarMap.values with
  | [κ] =>
    let initial : List (KVar × List (Expr × List Nat)) := [(κ, [(qGt, [0])])]
    let flat ← (exprFlat body).run kctx
    IO.println s!"\nWeaken-B (should KEEP):"
    IO.println s!"  input:     1 candidate"
    let after ← weakenOnce kctx flat initial
    for (_, cands) in after do
      IO.println s!"  survivors: {cands.length}   (expect 1)"
  | _ => IO.println "unexpected κ count"

  ----------------------------------------------------------------------
  -- Weaken-C: mixed starting set, exactly one survives.
  --
  -- Constraint: ∃ κ : Int → Prop, ∀ x : Int, x = 2 → κ x
  -- Candidates:
  --   (q_gt_one,  [0])  – expect KEEP  (x = 2 ⇒ x > 1)
  --   (q_lt_zero, [0])  – expect DROP  (x = 2 does NOT ⇒ x < 0)
  ----------------------------------------------------------------------
  let qLt ← mkConstWithLevelParams ``_wt_lt_zero
  let goalMVar3 ← mkFreshExprMVar (some stmt2)
  let (kvarMap, _kvarsRev, bodyGoalId) ← peelExistentialsAndIntro goalMVar3.mvarId!
  let body ← bodyGoalId.getType
  let kctx : KContext := { kvars := kvarMap }
  match kvarMap.values with
  | [κ] =>
    let initial : List (KVar × List (Expr × List Nat)) :=
      [(κ, [(qGt, [0]), (qLt, [0])])]
    let flat ← (exprFlat body).run kctx
    IO.println s!"\nWeaken-C (mixed, should keep exactly 1):"
    IO.println s!"  input:     2 candidates  (q_gt_one, q_lt_zero)"
    let after ← weakenOnce kctx flat initial
    for (_, cands) in after do
      IO.println s!"  survivors: {cands.length}   (expect 1 — only q_gt_one)"
  | _ => IO.println "unexpected κ count"

run_cmd Lean.Elab.Command.liftTermElabM do
  -- Same minimal example as Weaken-B: κ x is seeded by x = 2, never mutated.
  -- Expected: after PA, κ's solution is a conjunction of the (few) qualifiers
  -- that hold for `x = 2`. Notably includes `x > 1`; excludes `x < 0`.
  let stmt ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, x = 2 → κ x)) none
  let goalMVar ← mkFreshExprMVar (some stmt)
  let (kvarMap, _kvarsRev, bodyGoalId) ← peelExistentialsAndIntro goalMVar.mvarId!
  let body ← bodyGoalId.getType
  let kctx : KContext := { kvars := kvarMap }
  match kvarMap.values with
  | [κ] =>
    let flat ← (exprFlat body).run kctx
    IO.println s!"\nPA-1:"
    let sols ← predicateAbstraction kctx [κ] flat
    for (κ', solExpr) in sols do
      IO.println s!"  κ = {κ'.name}"
      IO.println s!"  sol = {← ppExpr solExpr}"
  | _ => IO.println "unexpected κ count"
