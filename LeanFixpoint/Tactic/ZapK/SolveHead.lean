import LeanFixpoint.Tactic.ZapK.Step
import LeanFixpoint.Core.Types
import LeanFixpoint.Tactic.Internal.Utils
import LeanFixpoint.Elab.FromExpr
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr


open Lean Meta Elab Tactic

/-- Discharge a `?κ ȳ`-headed goal using a path that mirrors `sol`'s structure.

    Precondition: `κ.mvarId` has been pre-assigned to `λ z̄. sol` upstream.
    The mvar identity check survives that assignment because we read the
    goal type via `goal.getType` (raw) before any `whnf`.

    Pipeline:
      1. Verify the goal is `?κ ȳ`.
      2. Manually β-unfold: `instantiateMVars` expands `?κ` to the assigned
         lambda; `whnf` β-reduces `(λ z̄. sol) ȳ` to `sol[z̄ := ȳ]`.
      3. Replay `π`: each `doStep` peels one ∃/∧/∨ layer.
      4. Close the equality leaf (`⋀ᵢ yᵢ = yᵢ` after β) by `rfl` / `grind`. -/
def solveHead (κ : KVar) (sol : Expr) (π : Path) : TacticM Unit := withMainContext do
  let goal    ← getMainGoal
  let target  ← goal.getType
  unless target.getAppFn.isMVar &&
         target.getAppFn.mvarId! == κ.mvarId do
    throwError m!"solveHead: expected ?{κ.name}-headed goal, got\n {target}"
  -- LATE assignment: assign κ here, just before β-unfold. Until this
  -- point ?κ is unassigned, so refines/intros upstream can't unfold it.
  let lam ← solToWitnessExpr sol κ.params κ.paramTypes
  κ.mvarId.assign lam
  let beta ← whnf (← instantiateMVars target)
  let newGoal ← goal.change beta
  replaceMainGoal [newGoal]
  for step in π do doStep step


-- TESTING

private def mkExistsExpr (name : Name) (τ : Expr) (body : Expr → MetaM Expr) :
    MetaM Expr := do
  let predLam ← withLocalDeclD name τ fun x => do
    let b ← body x
    mkLambdaFVars #[x] b
  mkAppM ``Exists #[predLam]

private def mkLambdaExpr (name : Name) (τ : Expr) (body : Expr → MetaM Expr) :
    MetaM Expr := do
  withLocalDeclD name τ fun x => do
    let b ← body x
    mkLambdaFVars #[x] b

private def mkAndE (a b : Expr) : MetaM Expr := mkAppM ``And #[a, b]
private def mkOrE  (a b : Expr) : MetaM Expr := mkAppM ``Or  #[a, b]

/-- End-to-end test of `solveHead`:

    1. Peel the outer `∃ κ : Int → Prop` to expose a fresh κ-mvar.
    2. Intro `x : Int` and `hx : x = 1` from the body.
    3. Assign κ := `fun z => ∃ y, y = 1 ∧ y = z` (a hand-rolled "sol").
    4. Goal is now `?κ x`. Call `solveHead κ [exV x, conjH hx]`.

    Expected trace inside solveHead:
      ?κ x
        ── β-unfold ──▶  ∃ y : Int, y = 1 ∧ y = x
        ── doStep .exV x   ──▶  x = 1 ∧ x = x
        ── doStep .conjH hx ──▶  x = x
        ── rfl ──▶  closed -/
syntax "testSolveHead" : tactic

elab_rules : tactic
  | `(tactic| testSolveHead) => do
      let goal ← getMainGoal
      let (_kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
      match kvarsInOrder with
      | [κ] =>
          replaceMainGoal [bodyGoal]
          let (xFid, g1)  ← (← getMainGoal).intro1
          replaceMainGoal [g1]
          let (hxFid, g2) ← (← getMainGoal).intro1
          replaceMainGoal [g2]
          -- Build sol = fun z : Int => ∃ y : Int, y = 1 ∧ y = z
          let intTy := mkConst ``Int
          let one := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
          let solExpr ← withLocalDeclD `z intTy fun z => do
            let exBody ← withLocalDeclD `y intTy fun y => do
              let eq1 ← mkEq y one
              let eq2 ← mkEq y z
              let conj ← mkAppM ``And #[eq1, eq2]
              mkLambdaFVars #[y] conj
            let ex ← mkAppM ``Exists #[exBody]
            mkLambdaFVars #[z] ex
          κ.mvarId.assign solExpr
          let path : Path := [.exV (.fvar xFid), .conjH (.fvar hxFid)]
          solveHead κ solExpr path
      | _ =>
          throwError m!"testSolveHead: expected exactly 1 κ, got {kvarsInOrder.length}"

-- /-- Smallest end-to-end exercise of solveHead. -/
-- example : ∃ κ : Int → Prop, ∀ x : Int, x = 1 → κ x := by
--   testSolveHead
--   rfl

-- syntax "testSolveHead2" : tactic

-- elab_rules : tactic
--   | `(tactic| testSolveHead2) => withMainContext do
--       let goal ← getMainGoal
--       let (_, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
--       match kvarsInOrder with
--       | [κ] =>
--           replaceMainGoal [bodyGoal]
--           -- Intro x, hx, y, hy
--           let (xFid,  g1) ← (← getMainGoal).intro1; replaceMainGoal [g1]
--           let (hxFid, g2) ← (← getMainGoal).intro1; replaceMainGoal [g2]
--           let (yFid,  g3) ← (← getMainGoal).intro1; replaceMainGoal [g3]
--           let (hyFid, g4) ← (← getMainGoal).intro1; replaceMainGoal [g4]

--           -- sol := λ z₁ z₂. ∃ a, a = 1 ∧ ∃ b, b = 2 ∧ z₁ = a ∧ z₂ = b
--           let intTy := mkConst ``Int
--           let one := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
--           let two := mkApp (mkConst ``Int.ofNat) (mkNatLit 2)
--           let sol ← mkLambdaExpr `z₁ intTy fun z₁ =>
--             mkLambdaExpr `z₂ intTy fun z₂ =>
--               mkExistsExpr `a intTy fun a => do
--                 let aEq ← mkEq a one
--                 let inner ← mkExistsExpr `b intTy fun b => do
--                   let bEq    ← mkEq b two
--                   let z₁Eqa  ← mkEq z₁ a
--                   let z₂Eqb  ← mkEq z₂ b
--                   mkAndE bEq (← mkAndE z₁Eqa z₂Eqb)
--                 mkAndE aEq inner
--           κ.mvarId.assign sol

--           let path : Path :=
--             [.exV (.fvar xFid), .conjH (.fvar hxFid),
--              .exV (.fvar yFid), .conjH (.fvar hyFid)]
--           solveHead κ path
--       | _ => throwError m!"testSolveHead2: expected 1 κ, got {kvarsInOrder.length}"

-- example :
--     ∃ κ : Int → Int → Prop,
--       ∀ x : Int, x = 1 → ∀ y : Int, y = 2 → κ x y := by
--   testSolveHead2
--   constructor<;> rfl

-- syntax "testSolveHead3" : tactic

-- elab_rules : tactic
--   | `(tactic| testSolveHead3) => withMainContext do
--       let goal ← getMainGoal
--       let (_, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
--       match kvarsInOrder with
--       | [κ] =>
--           replaceMainGoal [bodyGoal]
--           let (xFid,  g1) ← (← getMainGoal).intro1; replaceMainGoal [g1]
--           let (hxFid, g2) ← (← getMainGoal).intro1; replaceMainGoal [g2]

--           -- sol := λ z. (∃ a, a = 0 ∧ z = a) ∨ (∃ a, a = 1 ∧ z = a)
--           let intTy := mkConst ``Int
--           let zero := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
--           let one  := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
--           let sol ← mkLambdaExpr `z intTy fun z => do
--             let leftDisj ← mkExistsExpr `a intTy fun a => do
--               let aEq0  ← mkEq a zero
--               let zEqa  ← mkEq z a
--               mkAndE aEq0 zEqa
--             let rightDisj ← mkExistsExpr `a intTy fun a => do
--               let aEq1  ← mkEq a one
--               let zEqa  ← mkEq z a
--               mkAndE aEq1 zEqa
--             mkOrE leftDisj rightDisj
--           κ.mvarId.assign sol

--           let path : Path :=
--             [.inR, .exV (.fvar xFid), .conjH (.fvar hxFid)]
--           solveHead κ path
--       | _ => throwError m!"testSolveHead3: expected 1 κ"

-- example : ∃ κ : Int → Prop, ∀ x : Int, x = 1 → κ x := by
--   testSolveHead3
--   rfl

-- syntax "testSolveHead4" : tactic

-- elab_rules : tactic
--   | `(tactic| testSolveHead4) => withMainContext do
--       let goal ← getMainGoal
--       let (_, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
--       match kvarsInOrder with
--       | [κ] =>
--           replaceMainGoal [bodyGoal]
--           let (xFid,  g1) ← (← getMainGoal).intro1; replaceMainGoal [g1]
--           let (hxFid, g2) ← (← getMainGoal).intro1; replaceMainGoal [g2]

--           -- sol := λ z. ((∃ a, a = 0 ∧ z = a) ∨ (∃ a, a = 1 ∧ z = a))
--           --             ∨ (∃ a, a = 2 ∧ z = a)
--           let intTy := mkConst ``Int
--           let zero := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
--           let one  := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
--           let two  := mkApp (mkConst ``Int.ofNat) (mkNatLit 2)
--           let mkBranch (lit : Expr) : MetaM Expr :=
--             mkExistsExpr `a intTy fun a => do
--               let aEq    ← mkEq a lit
--               let inner  := a  -- dummy, will use z below
--               -- Actually let's restructure
--               return ← do
--                 let aEq ← mkEq a lit
--                 pure aEq  -- placeholder, won't compile - rewrite
--           -- Simpler inline:
--           let sol ← mkLambdaExpr `z intTy fun z => do
--             let mkProd (lit : Expr) : MetaM Expr :=
--               mkExistsExpr `a intTy fun a => do
--                 let aEq  ← mkEq a lit
--                 let zEqa ← mkEq z a
--                 mkAndE aEq zEqa
--             let p0 ← mkProd zero
--             let p1 ← mkProd one
--             let p2 ← mkProd two
--             let leftHalf ← mkOrE p0 p1
--             mkOrE leftHalf p2
--           κ.mvarId.assign sol

--           let path : Path :=
--             [.inL, .inR, .exV (.fvar xFid), .conjH (.fvar hxFid)]
--           solveHead κ path
--       | _ => throwError m!"testSolveHead4: expected 1 κ"

-- example : ∃ κ : Int → Prop, ∀ x : Int, x = 1 → κ x := by
--   testSolveHead4
--   rfl
