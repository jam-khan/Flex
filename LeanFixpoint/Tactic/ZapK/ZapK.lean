import LeanFixpoint.Tactic.ZapK.Step
import LeanFixpoint.Tactic.ZapK.SolveHead
import LeanFixpoint.Tactic.RewriteKs
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr

open Lean Meta Elab Tactic

/-- Walk the goal structurally; at κ-heads (for any κ in `kvars`),
    invoke `solveHead`. Foreign mvars and non-κ leaves are left as
    residual goals — `zapk` is purely structural and does not close
    obligations.

    Convention: `kvars` is processed in topological order, with each
    κ already pre-assigned to `λ z̄. sol_i` (sol unsimplified, per the
    duality contract).

    Does not call `instantiateMVars` on the goal type — `?κ`-form must
    survive across κ-assignment for identity-based dispatch. -/
partial def zapk (kSols : List (KVar × Expr)) (π : Path := []) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)

  -- (a) κ-head leaf for one of OUR κs
  if target.getAppFn.isMVar then
    if let some (κ, sol) := kSols.find?
        (fun (κ, _) => κ.mvarId == target.getAppFn.mvarId!) then
      solveHead κ sol π
    return  -- foreign mvar: residual

  -- (b) ∧, (c) ∀ (value or prop), (d) residual — unchanged except recursive
  -- calls now pass kSols instead of kvars.
  if target.and?.isSome then
    evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
    let goals ← getGoals
    let gℓ := goals[0]!
    let gᵣ := goals[1]!
    let rest := goals.drop 2
    setGoals [gℓ]; zapk kSols (π ++ [.inL])
    let leftRes ← getGoals
    setGoals [gᵣ]; zapk kSols (π ++ [.inR])
    let rightRes ← getGoals
    setGoals (leftRes ++ rightRes ++ rest)
    return

  if target.isForall then
    let dom := target.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    let (fid, newGoal) ← goal.intro1
    replaceMainGoal [newGoal]
    let step := if domSort.isProp
                  then Step.conjH (.fvar fid)
                  else Step.exV (.fvar fid)
    zapk kSols (π ++ [step])
    return

  return


syntax "testZapk" : tactic

elab_rules : tactic
  | `(tactic| testZapk) => withMainContext do
      let goal ← getMainGoal
      let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
      let kctx : KContext := { kvars := kvarMap }
      replaceMainGoal [bodyGoal]

      -- Phase 1: compute all sols and build their closed lambdas, but
      -- DO NOT assign yet. (No simplifyExpr — duality requires unsimplified sol.)
      let mut curr ← (← getMainGoal).getType
      let mut kSols : List (KVar × Expr) := []
      for κ in kvarsInOrder do
        let scoped' ← (exprScope κ curr).run kctx
        let sol    ← (exprSol1 κ scoped').run kctx
        let lam ← solToWitnessExpr sol κ.params κ.paramTypes
        kSols := kSols ++ [(κ, lam)]
        curr ← (exprElimStar κ sol curr).run kctx

      -- Phase 2: structural proof; solveHead assigns each κ on demand
      -- (just before β-unfolding at its κ-head leaf).
      zapk kSols

/-- ex1 from Demo/Basic.lean — single κ, mixed producer/consumer. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  testZapk
  · constructor <;> rfl
  · grind

example :
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  testZapk
  · constructor <;> rfl
  · constructor <;> rfl
  · grind
  · grind


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
  testZapk
  · trivial
  · trivial
  · sorry
  · grind
