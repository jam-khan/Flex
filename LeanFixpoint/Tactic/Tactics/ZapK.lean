import LeanFixpoint.Tactic.Tactics.RewriteKs
import LeanFixpoint.Core
import LeanFixpoint.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Zap

open Lean Meta Elab Tactic

syntax "zapK" : tactic

elab_rules : tactic
  | `(tactic| zapK) => withMainContext do
      -- Phase 1: peel ∃κ binders and compute lam_κᵢ for each κᵢ.
      let goal ← getMainGoal
      let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
      let kctx : KContext := { kvars := kvarMap }
      replaceMainGoal [bodyGoal]
      let mut curr ← (← getMainGoal).getType
      let mut kLams : List (KVar × Expr) := []
      for κ in kvarsInOrder do
        -- Use ZapK-local preserve-And variants so sol's Or-tree mirrors
        -- the goal's full And-tree. (Fusion.lean's `exprScope`/`exprSol1`
        -- strip non-κ branches — fine for solve_fixpoint, wrong for us.)
        let scoped' ← (exprScopePres κ curr).run kctx
        let sol    ← (exprSol1Pres κ scoped').run kctx
        -- Drop dead κ-references from sol (e.g. `(κⱼ y x) ∧ False`)
        -- without collapsing the Or-tree — preserves path-mirror.
        let sol    := simplifyAndExists sol
        let lam    ← solToWitnessExpr sol κ.params κ.paramTypes
        kLams := kLams ++ [(κ, lam)]
        curr   ← (exprElimStar κ sol curr).run kctx

      -- Phase 2: assign each κ-mvar to its lam directly.
      -- (Let-binding UX deferred — would require κ-mvar lctx surgery.)
      for (κ, lam) in kLams do
        κ.mvarId.assign lam

      -- Phase 3: single walk emitting the proof.
      let bodyTy ← (← getMainGoal).getType
      let residualOut ← IO.mkRef #[]
      let proof ← walkProof kLams bodyTy [] [] [] residualOut
      (← getMainGoal).assign proof
      replaceMainGoal (← residualOut.get).toList

-- ───────────────────────────────────────────────────────────────────────
-- Tests (ported from old ZapK.lean)
-- ───────────────────────────────────────────────────────────────────────

/-- ex1-style: single κ, mixed producer/consumer. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zapK
  all_goals first | rfl | grind

/-- ex6-style: two independent κs, four conjuncts. -/
example :
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  zapK
  all_goals first | rfl | grind

/-- ex2-style: two κs with cross-flow. -/
example :
    ∃ κx : Int → Int → Int → Int → Prop, ∃ κy : Int → Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ n : Int,
        n = x - 1 →
        ∀ p : Int,
          p = x + 1 →
          ( (∀ ν : Int, ν = n → κx ν x n p)
          ∧ (∀ ν : Int, ν = p → κy ν x n p)
          ∧ (∀ ν : Int, κx ν x n p → κy ν x n p)
          ∧ (∀ y : Int, κy y x n p →
              ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
          ) := by
  zapK
  all_goals first | rfl | grind
