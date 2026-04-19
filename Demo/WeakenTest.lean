import LeanFixpoint
import LeanFixpoint.Solve.Weaken

open Lean Meta Elab Term

-- Dedicated qualifiers for testing. Separate from FibFibFast's q_gt_one etc.
-- so the environment tagset stays predictable.
@[qualif] private def _wt_gt_one (v : Int)    : Prop := v > 1
@[qualif] private def _wt_le     (a b : Int)  : Prop := a ≤ b
@[qualif] private def _wt_eq     (a b : Int)  : Prop := a = b

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
  peelExistentials stmt {} fun kvarMap body => do
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

  ----------------------------------------------------------------------
  -- A: simplest — 1-arg κ, single clause with head-only κ-app
  ----------------------------------------------------------------------
  let sA ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, κ x)) none
  runSpec "A  1-arg κ, head-only, q_gt_one at [0]" sA qGt [0]
  -- Expect: ∀ x : Int, x > 1

  ----------------------------------------------------------------------
  -- B: 1-arg κ, hypothesis (non-κ) + head
  ----------------------------------------------------------------------
  let sB ← elabTerm (← `(∃ κ : Int → Prop, ∀ x : Int, 0 ≤ x → κ x)) none
  runSpec "B  1-arg κ, (0 ≤ x) → κ x,   q_gt_one at [0]" sB qGt [0]
  -- Expect: ∀ x : Int, 0 ≤ x → x > 1

  ----------------------------------------------------------------------
  -- C: 2-arg κ, q_le at [0, 1] — identity slot mapping
  ----------------------------------------------------------------------
  let sC ← elabTerm (← `(∃ κ : Int → Int → Prop, ∀ a b : Int, κ a b)) none
  runSpec "C  2-arg κ, q_le at [0, 1]" sC qLe [0, 1]
  -- Expect: ∀ a b : Int, a ≤ b

  ----------------------------------------------------------------------
  -- D: same clause, reversed slot mapping (b ≤ a) — tests slot perm
  ----------------------------------------------------------------------
  runSpec "D  2-arg κ, q_le at [1, 0]  (slot reversal)" sC qLe [1, 0]
  -- Expect: ∀ a b : Int, b ≤ a

  ----------------------------------------------------------------------
  -- E: 4-arg κ, 1-ary qualifier bound to middle slot — ghost args [0,1,3]
  ----------------------------------------------------------------------
  let sE ← elabTerm (← `(∃ κ : Int → Int → Int → Int → Prop,
                           ∀ a b c d : Int, κ a b c d)) none
  runSpec "E  4-arg κ, q_gt_one at [2]  (ghost args 0,1,3)" sE qGt [2]
  -- Expect: ∀ a b c d : Int, c > 1

  ----------------------------------------------------------------------
  -- F: 1-arg κ, chained foralls — verifies scoping preservation
  ----------------------------------------------------------------------
  let sF ← elabTerm (← `(∃ κ : Int → Prop,
                           ∀ x : Int, 0 ≤ x → ∀ y : Int, y = x + 1 → κ y)) none
  runSpec "F  1-arg κ, chained ∀ and hyps, q_gt_one at [0]" sF qGt [0]
  -- Expect: ∀ x, 0 ≤ x → ∀ y, y = x + 1 → y > 1

  ----------------------------------------------------------------------
  -- G: 2-arg κ, clause with TWO head κ-apps in conjunction
  ----------------------------------------------------------------------
  let sG ← elabTerm (← `(∃ κ : Int → Int → Prop,
                           ∀ a b : Int, κ a b ∧ κ b a)) none
  runSpec "G  2-arg κ, conj (κ a b ∧ κ b a), q_le at [0, 1]" sG qLe [0, 1]
  -- exprFlat should split this into 2 clauses:
  --   clause 0: ∀ a b, κ a b  →  ∀ a b, a ≤ b
  --   clause 1: ∀ a b, κ b a  →  ∀ a b, b ≤ a
  -- (remember: the head args of clause 1 are (b, a), so with qSlots=[0,1]
  --  we project [b, a] and β-apply q_le → b ≤ a. Slot reversal happens
  --  *automatically* because the κ-app in the clause uses (b, a), not (a, b).)

  ----------------------------------------------------------------------
  -- H: FibFibFast-shaped seed clause — 4-arg κ, constants as head args
  ----------------------------------------------------------------------
  let sH ← elabTerm (← `(∃ κ : Int → Int → Int → Int → Prop,
                           ∀ n : Int, n ≥ 0 → κ 2 1 2 n)) none
  runSpec "H  FibFibFast seed shape, q_le at [0, 3]" sH qLe [0, 3]
  -- Expect: ∀ n : Int, n ≥ 0 → 2 ≤ n
  -- (args = #[2, 1, 2, n]; qSlots=[0,3] picks 2 and n; q_le 2 n = 2 ≤ n.)
  
