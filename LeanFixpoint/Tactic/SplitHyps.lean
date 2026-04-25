import Lean

open Lean Elab Tactic Meta

/--
  One pass over the local context: for every hypothesis whose
  type reduces to `_ ∧ _`, destruct it via `rcases`.

  Returns `true` iff at least one hypothesis was split.

  Ignore any auxillary declarations in hypotheses.
-/
private def splitHypsAndsPass : TacticM Bool := withMainContext do
  -- track if split occured or not
  let mut didSplit := false
  -- get local context, and
  -- iterate through local declarations
  for localDecl in ← getLCtx do
    -- get type of local declaration
    -- note: `whnf` vs. `whnfR`, latter only reduces defs tagged with @reducible
    let type ← whnf (← instantiateMVars localDecl.type)
    -- check if localdef is auxillary, or it is not `_ ∧ _`, skip
    if localDecl.isAuxDecl || !type.isAppOfArity ``And 2 then continue
    -- get hypothesis
    let hName := mkIdent localDecl.userName
    -- create binders for left and right split of `∧`
    let lName := mkIdent (← Term.mkFreshBinderName)
    let rName := mkIdent (← Term.mkFreshBinderName)
    -- perform split
    evalTactic (← `(tactic| rcases $hName:ident with ⟨$lName:ident, $rName:ident⟩))
    didSplit := true
  return didSplit

/--
  Run `splitHypsAndsPass` repeatedly. If `maxDepth` is `some k`, stop
  after at most `k` passes; if `none`, run to exhaustion. Returns `true`
  iff at least one pass made progress.
-/
private partial def splitHypAndsLoop (depth: Option Nat) : TacticM Bool :=
  match depth with
  | some 0  => return false
  | depth   => do
    if ← splitHypsAndsPass then
      -- why map? depth is wrapped in option
      let _ ← splitHypAndsLoop (depth.map (· - 1))
      return true
    else
      return false

/-- `split_hyp_ands`               — exhaustively split `∧` hypotheses.
    `split_hyp_ands <n>`           — split up to `n` passes deep.

    Throws `"no conjunctions found in hypotheses"` iff there was no `∧`
    hypothesis to split (so the tactic composes correctly inside
    `first | … | …`). -/
syntax "split_hyp_ands" (num)? : tactic

-- Helper to run splitHypsAndsLoop
private def runWithDepth (depth : Option Nat) : TacticM Unit := do
  unless ← splitHypAndsLoop depth do
    throwError "no conjunctions found in hypotheses"

elab_rules : tactic
  | `(tactic| split_hyp_ands)        => runWithDepth none
  | `(tactic| split_hyp_ands $n:num) => runWithDepth (some n.getNat)


-- Each `example` is checked at compile time; if any of these stop closing,
-- `split_hyp_ands` regressed.
section SplitHypAndsTests

example (P Q : Prop) (h : P ∧ Q) : P := by
  split_hyp_ands
  assumption

example (P Q : Prop) (h : P ∧ Q) : Q := by
  split_hyp_ands
  assumption

-- Right-associated nested conjunction: needs ≥2 passes to fully split.
example (P Q R : Prop) (h : P ∧ Q ∧ R) : P ∧ R := by
  split_hyp_ands
  refine ⟨?_, ?_⟩ <;> assumption

-- Multiple top-level ∧ hypotheses split in a single pass.
example (P Q R S : Prop) (h₁ : P ∧ Q) (h₂ : R ∧ S) : Q ∧ S := by
  split_hyp_ands
  refine ⟨?_, ?_⟩ <;> assumption

-- Bounded depth: `1` peels only the outer ∧; the inner Q ∧ R is left alone.
example (P Q R : Prop) (h : P ∧ Q ∧ R) : P := by
  split_hyp_ands 1
  assumption

-- Non-∧ hypotheses are ignored, not consumed.
example (P Q : Prop) (hPQ : P ∧ Q) (_hP : P → True) : Q := by
  split_hyp_ands
  -- _hP is still in context as an arrow, untouched
  assumption

-- Hypothesis whose type definitionally unfolds to `_ ∧ _` is also caught,
-- because the loop uses `whnf`.
example (P Q : Prop) (h : id (P ∧ Q)) : P := by
  split_hyp_ands
  assumption

end SplitHypAndsTests

/--
  Cases on the first `∨` hypothesis of `g`'s context, producing
  one goal per disjunct, and recursively splits each resulting
  goal until no `∨` hypothesis remains. Returns the final
  goal list. If `g` has no `∨` hypothesis at all,
  returns `[g]` unchanged.

  The `Option Nat` argument bounds the recursion depth: `some k`
  stops after at most `k` rounds of `cases`;
  `none` runs to exhaustion
-/
private partial def splitHypOrsOnGoal
  (depth : Option Nat)
  (g : MVarId) : TacticM (List MVarId × Bool) :=
    match depth, g with
    | some 0, g => pure ([g], false)
    | depth, g  =>
      g.withContext do
        let mut didSplit := false
        for localDecl in ← getLCtx do
          let type ← whnf (← instantiateMVars localDecl.type)
          if localDecl.isAuxDecl || !type.isAppOfArity ``Or 2 then continue
          let hName := mkIdent localDecl.userName
          setGoals [g]
          evalTactic (← `(tactic| cases $hName:ident))
          didSplit := true
          break
        unless didSplit do return ([g], false)
        let mut result : List MVarId := []
        for g' in ← getGoals do
          let (gs, _) ← splitHypOrsOnGoal (depth.map (· - 1)) g'
          result := result ++ gs
        return (result, true)

/-- `split_hyp_ors`     — exhaustively `cases` every `∨` hypothesis,
                          producing one goal per branch combination.
    `split_hyp_ors <n>` — bound the recursion to `n` rounds of `cases`.

    Throws `"no disjunctions found in hypotheses"` if no `∨` hypothesis
    exists — required so the tactic composes inside `first | … | …`.
    Matches `_ ∨ _` up to default-transparency unfolding.

    Examples:
    ```
    example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
      split_hyp_ors
      · right; assumption
      · left;  assumption

    example (P Q R : Prop) (h : P ∨ (Q ∨ R)) : True := by
      split_hyp_ors 1   -- only outer ∨; inner remains as `_ ∨ _`
      · trivial
      · trivial
    ```
-/
syntax "split_hyp_ors" (num)? : tactic

private def splitHypsOrsRunWithDepth (depth : Option Nat) : TacticM Unit := do
  let main ← getMainGoal
  let rest := (← getGoals).tail!
  let (resulting, didAny) ← splitHypOrsOnGoal depth main
  unless didAny do
    throwError "no disjunctions found in hypotheses"
  setGoals (resulting ++ rest)

elab_rules : tactic
  | `(tactic| split_hyp_ors)        => splitHypsOrsRunWithDepth none
  | `(tactic| split_hyp_ors $n:num) => splitHypsOrsRunWithDepth (some n.getNat)

-- ─── Tests: split_hyp_ors ───────────────────────────────────────────────

section SplitHypOrsTests

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  split_hyp_ors
  · right; assumption
  · left;  assumption

-- Nested ∨ exhaustively peeled to three branches.
example (P Q R : Prop) (h : P ∨ (Q ∨ R)) : R ∨ Q ∨ P := by
  split_hyp_ors
  · right; right; assumption
  · right; left;  assumption
  · left;         assumption

-- Bounded depth: only the outer ∨; inner ∨ left intact.
example (P Q R : Prop) (h : P ∨ (Q ∨ R)) : True := by
  split_hyp_ors 1
  · trivial
  · trivial

-- Multiple top-level ∨s — split combinatorially.
example (P Q R S : Prop) (h₁ : P ∨ Q) (h₂ : R ∨ S) : True := by
  split_hyp_ors
  all_goals trivial

-- Default-transparency unfolding catches `id (P ∨ Q)`.
example (P Q : Prop) (h : id (P ∨ Q)) : Q ∨ P := by
  split_hyp_ors
  · right; assumption
  · left;  assumption

end SplitHypOrsTests

-- ─── split_hyp_exists ──────────────────────────────────────────────────

/-- One pass over the local context: for every hypothesis whose type
    head-reduces to `∃ x, _`, destructure it via `rcases h with ⟨x, h⟩`.
    Returns `true` iff at least one hypothesis was split. Auxiliary
    declarations are skipped. -/
private def splitHypExistsPass : TacticM Bool := withMainContext do
  let mut didSplit := false
  for localDecl in ← getLCtx do
    let type ← whnf (← instantiateMVars localDecl.type)
    if localDecl.isAuxDecl || !type.isAppOfArity ``Exists 2 then continue
    let hName := mkIdent localDecl.userName
    let wName := mkIdent (← Term.mkFreshBinderName)
    let bName := mkIdent (← Term.mkFreshBinderName)
    evalTactic (← `(tactic| rcases $hName:ident with ⟨$wName:ident, $bName:ident⟩))
    didSplit := true
  return didSplit

/-- Run `splitHypExistsPass` repeatedly. If `maxDepth` is `some k`, stop
    after at most `k` passes; if `none`, run to exhaustion. Returns `true`
    iff at least one pass made progress. -/
private partial def splitHypExistsLoop : Option Nat → TacticM Bool
  | some 0 => return false
  | depth  => do
    if ← splitHypExistsPass then
      let _ ← splitHypExistsLoop (depth.map (· - 1))
      return true
    else
      return false

/-- `split_hyp_exists`     — exhaustively destructure every `∃` hypothesis.
    `split_hyp_exists <n>` — do at most `n` passes (each pass destructures
                             every `∃` currently in scope).

    Throws `"no existential statements found in hypotheses"` if there is
    no `∃` hypothesis to split — required so the tactic composes inside
    `first | … | …`. Matches `∃ x, _` up to default-transparency unfolding.

    Examples:
    ```
    example (P : Nat → Prop) (h : ∃ x, P x) : ∃ y, P y := by
      split_hyp_exists      -- now: w : Nat, b : P w
      exact ⟨_, by assumption⟩

    example (P : Nat → Nat → Prop) (h : ∃ x y, P x y) : ∃ a b, P a b := by
      split_hyp_exists 1    -- one pass: peels outer ∃ only
      exact ⟨_, by assumption⟩
    ```
-/
syntax "split_hyp_exists" (num)? : tactic

private def splitHypExistsRunWithDepth (depth : Option Nat) : TacticM Unit := do
  unless ← splitHypExistsLoop depth do
    throwError "no existential statements found in hypotheses"

elab_rules : tactic
  | `(tactic| split_hyp_exists)        => splitHypExistsRunWithDepth none
  | `(tactic| split_hyp_exists $n:num) => splitHypExistsRunWithDepth (some n.getNat)

-- ─── Tests: split_hyp_exists ────────────────────────────────────────────

section SplitHypExistsTests

example (P : Nat → Prop) (h : ∃ x, P x) : ∃ y, P y := by
  split_hyp_exists
  exact ⟨_, by assumption⟩

-- Two top-level existentials split in one pass.
example (P Q : Nat → Prop) (h₁ : ∃ x, P x) (h₂ : ∃ y, Q y) :
    ∃ x y, P x ∧ Q y := by
  split_hyp_exists
  exact ⟨_, _, by assumption, by assumption⟩

-- Nested: `∃ x y, P x y` needs two passes to fully peel.
example (P : Nat → Nat → Prop) (h : ∃ x y, P x y) : ∃ a b, P a b := by
  split_hyp_exists
  exact ⟨_, _, by assumption⟩

-- Bounded depth: only outer ∃ peeled.
example (P : Nat → Nat → Prop) (h : ∃ x y, P x y) :
    ∃ x, ∃ y, P x y := by
  split_hyp_exists 1
  exact ⟨_, by assumption⟩

-- Non-∃ hypotheses are ignored.
example (P : Nat → Prop) (h : ∃ x, P x) (_k : Nat) : ∃ y, P y := by
  split_hyp_exists
  exact ⟨_, by assumption⟩

-- Default-transparency unfolding catches `id (∃ x, _)`.
example (P : Nat → Prop) (h : id (∃ x, P x)) : ∃ y, P y := by
  split_hyp_exists
  exact ⟨_, by assumption⟩

end SplitHypExistsTests

-- ─── Composing macros ──────────────────────────────────────────────────

/-- `split_hyp_and_exist` — repeat `split_hyp_ands` and `split_hyp_exists`
    until neither makes progress. Useful when you have `∧`/`∃` chains but
    don't want `∨` to fork the goal list. -/
macro "split_hyp_and_exist" : tactic =>
  `(tactic| repeat (first | split_hyp_ands | split_hyp_exists))

/-- `split_hyps` — repeat all three split tactics across all goals until
    no compound hypothesis (`∧`, `∨`, `∃`) remains anywhere. -/
macro "split_hyps" : tactic =>
  `(tactic| repeat (any_goals (first
      | split_hyp_ands
      | split_hyp_ors
      | split_hyp_exists)))

-- ─── Tests: split_hyps ──────────────────────────────────────────────────

section SplitHypsTests

-- Hard #1: a single deeply-nested mixed hypothesis (∃ → ∧ → ∨).
-- Forces the macro to: peel ∃, split ∧, then `cases` ∨ — in that order,
-- across passes. The goal flips the disjunction (Q ∨ R → R ∨ Q) so each
-- branch must actively use the *right* disjunct, not just any closer.
example (P Q R : Nat → Prop) (h : ∃ x, P x ∧ (Q x ∨ R x)) :
    ∃ y, P y ∧ (R y ∨ Q y) := by
  split_hyps
  -- Two goals, one per `∨` branch:
  --   Goal 1 (inl): w : Nat, hP : P w, hQ : Q w
  --   Goal 2 (inr): w : Nat, hP : P w, hR : R w
  · exact ⟨_, by assumption, .inr (by assumption)⟩
  · exact ⟨_, by assumption, .inl (by assumption)⟩

-- Hard #2: multiple top-level hypotheses with cross-cutting connectives.
-- `h₁` is ∨ of two ∃s, `h₂` is ∧. Tests that:
--   * split_hyp_ors fires *before* the inner ∃s are visible,
--   * split_hyp_exists then fires per ∨-branch,
--   * split_hyp_ands chops h₂ into two atoms regardless of branch,
--   * `any_goals` keeps the macro pumping in each branch independently.
-- Goal mixes a ∃ at the top, a ∨ inside, and an atomic carry-through (R).
example (P Q : Nat → Prop) (R : Prop)
    (h₁ : (∃ x, P x) ∨ (∃ y, Q y)) (h₂ : R ∧ R) :
    ∃ z, (P z ∨ Q z) ∧ R := by
  split_hyps
  -- Two goals:
  --   Goal 1 (h₁ inl): w : Nat, hP : P w, hR₁ : R, hR₂ : R
  --   Goal 2 (h₁ inr): w : Nat, hQ : Q w, hR₁ : R, hR₂ : R
  · exact ⟨_, .inl (by assumption), by assumption⟩
  · exact ⟨_, .inr (by assumption), by assumption⟩

end SplitHypsTests
