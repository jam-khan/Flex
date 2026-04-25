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

-- ─── Tests ──────────────────────────────────────────────────────────────
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
