import LeanFixpoint.VCG.While.Hoare
import LeanFixpoint.Tactic.Zap
import LeanFixpoint.Tactic.Hoist
import LeanFixpoint.Tactic.SolveFusion
import LeanFixpoint.Tactic.SolveFixpoint

/-! # Constrained Horn Clause Generation

  `whileCHC vars pre c post` produces a Lean Prop that is a system of
  Constrained Horn Clauses.  `vars` is a fixed list of program variables
  (assignment targets plus any read-only variables such as loop bounds).
  Every existential — both `seq` midpoints and `cwhile` invariants — has
  type `NaryProp vars.length`, i.e. `Int → ... → Prop` with one argument
  per variable in `vars`.  The result is directly solvable by `solve_fixpoint`.

  Soundness: if the CHC system is satisfiable, then `ValidHoareTriple pre c post`.
-/

/-- Generate CHCs for a command.  `vars` fixes the shared arity for all
    existentials: every `seq` midpoint and every `cwhile` invariant has type
    `NaryProp vars.length`.  Use `(readOnlyVars ++ c.assignedVars).eraseDups`
    as a convenient default for `vars`.

    The output is a Lean `Prop` whose only existentials are `∃ κ : NaryProp vars.length`. -/
@[simp]
def whileCHC (vars : List CVar) (pre : Assertion) (c : Cmd) (post : Assertion) : Prop :=
  match c with
  | .skip =>
    ∀ s, pre s → post s

  | .assign x f =>
    ∀ s, pre s → post (s[x ↦ f s])

  | .seq c₁ c₂ =>
    ∃ κ : NaryProp vars.length,
      whileCHC vars pre c₁ (applyNary vars κ) ∧
      whileCHC vars (applyNary vars κ) c₂ post

  | .ite g c₁ c₂ =>
    whileCHC vars (fun s => pre s ∧ g s = true) c₁ post
    ∧ whileCHC vars (fun s => pre s ∧ g s = false) c₂ post

  | .cwhile g body =>
    ∃ κ : NaryProp vars.length,
      (∀ s, pre s → applyNary vars κ s)                                                   -- init
    ∧ whileCHC vars (fun s => applyNary vars κ s ∧ g s = true) body (applyNary vars κ)    -- preserve
    ∧ (∀ s, applyNary vars κ s ∧ g s = false → post s)                                    -- exit

/-- Soundness: if the CHC system is satisfiable, the Hoare triple holds. -/
@[simp]
theorem whileCHC_sound (vars : List CVar) (pre : Assertion) (c : Cmd) (post : Assertion) :
    whileCHC vars pre c post → ValidHoareTriple pre c post := by
  induction c generalizing pre post with
  | skip =>
    intro h s₁ s₂ heval hpre
    cases heval; exact h _ hpre
  | assign x f =>
    intro h s₁ s₂ heval hpre
    cases heval; exact h _ hpre
  | seq c₁ c₂ ih₁ ih₂ =>
    intro ⟨κ, h₁, h₂⟩
    exact hoare_seq (ih₁ _ _ h₁) (ih₂ _ _ h₂)
  | ite g c₁ c₂ ih₁ ih₂ =>
    intro ⟨h₁, h₂⟩
    exact hoare_if (ih₁ _ _ h₁) (ih₂ _ _ h₂)
  | cwhile g body ih =>
    intro ⟨κ, hinit, hpres, hpost⟩
    exact hoare_while hinit (ih _ _ hpres) hpost

/-! # Examples -/

-- Program: x := 0; while x < n do x := x + 1 end
-- Pre: 0 ≤ n, Post: x = n
def countToN : Cmd :=
  .seq (.assign "x" (fun _ => 0))
       (.cwhile (fun s => decide (s "x" < s "n"))
                (.assign "x" (fun s => s "x" + 1)))

@[qualif] def Le (i1 i2 : Int) : Prop := i1 ≤ i2

theorem flip_local : (∃ (κ κ_1 : Int → Int → Prop),
  (∀ (s : State), 0 ≤ s "n" → κ (s "n") 0) ∧
    (∀ (s : State), κ (s "n") (s "x") → κ_1 (s "n") (s "x")) ∧
      (∀ (s : State), κ_1 (s "n") (s "x") → s "x" < s "n" → κ_1 (s "n") (s "x" + 1)) ∧
        ∀ (s : State), κ_1 (s "n") (s "x") → s "n" ≤ s "x" → s "x" = s "n") =
  ∃ (κ_1 κ : Int → Int → Prop),
  (∀ (s : State), 0 ≤ s "n" → κ (s "n") 0) ∧
    (∀ (s : State), κ (s "n") (s "x") → κ_1 (s "n") (s "x")) ∧
      (∀ (s : State), κ_1 (s "n") (s "x") → s "x" < s "n" → κ_1 (s "n") (s "x" + 1)) ∧
        ∀ (s : State), κ_1 (s "n") (s "x") → s "n" ≤ s "x" → s "x" = s "n" := by
  apply propext ; apply Iff.intro
  intro ⟨k, k1, _⟩
  exists k1, k
  intro ⟨k1, k, _⟩
  exists k, k1

-- vars=["n","x"]: every ∃ has type Int → Int → Prop  (args: s "n", s "x")
example : ValidHoareTriple (fun s => 0 ≤ s "n") countToN (fun s => s "x" = s "n") := by
  apply whileCHC_sound ["n", "x"]
  dsimp [whileCHC, countToN, State.update, applyNary]
  simp
  hoist_exists
  rw [flip_local]
  under_exists1 =>
    solve_fusion
  solve_fixpoint

-- Program: while x ≠ 0 do x := x - 1 end
-- Pre: True, Post: x = 0
@[simp]
def reduceToZero : Cmd :=
  .cwhile (fun s => s "x" != 0)
          (.assign "x" (fun s => s "x" - 1))

set_option maxHeartbeats 1600000 in
-- vars=["x"]: κ : Int → Prop  (argument: s "x")
theorem reduceToZero_correct :
    ValidHoareTriple (fun _ => True) reduceToZero (fun s => s "x" = 0) := by
  apply whileCHC_sound ["x"]
  simp [whileCHC]
  solve_fixpoint

@[qualif]
def sumEq (i1 i2 i3 : Int) : Prop :=
  i1 + i2 = i3

@[qualif]
def sumEq1 (i1 i2 i3 : Int) : Prop :=
  i1 + (i2 + 1) = i3

@[qualif]
def Ge0 (i1 : Int) : Prop :=
  0 ≤ i1

-- Program: x := n; y := 0; while x ≠ 0 do x := x-1; y := y+1 end
-- Pre: 0 ≤ n, Post: y = n
-- vars=["n","x","y"]: every ∃ has type Int → Int → Int → Prop  (args: s "n", s "x", s "y")
def slowAssign : Cmd :=
  .seq (.assign "x" (fun s => s "n"))
  (.seq (.assign "y" (fun _ => 0))
  (.cwhile (fun s => s "x" != 0)
    (.seq (.assign "x" (fun s => s "x" - 1))
          (.assign "y" (fun s => s "y" + 1)))))

theorem flip_local_2 :
  (∃ (κ κ_1 κ_2 κ_3 : Int → Int → Int → Prop),
  (∀ (s : State), 0 ≤ s "n" → κ (s "n") (s "n") (s "y")) ∧
    (∀ (s : State), κ (s "n") (s "x") (s "y") → κ_1 (s "n") (s "x") 0) ∧
      (∀ (s : State), κ_1 (s "n") (s "x") (s "y") → κ_2 (s "n") (s "x") (s "y")) ∧
        (∀ (s : State), κ_2 (s "n") (s "x") (s "y") ∧ (s "x" != 0) = true → κ_3 (s "n") (s "x" - 1) (s "y")) ∧
          (∀ (s : State), κ_3 (s "n") (s "x") (s "y") → κ_2 (s "n") (s "x") (s "y" + 1)) ∧
            ∀ (s : State), κ_2 (s "n") (s "x") (s "y") ∧ (s "x" != 0) = false → s "y" = s "n") =
  (∃ κ_3 κ_2 κ κ_1 : Int → Int → Int → Prop,
  (∀ (s : State), 0 ≤ s "n" → κ (s "n") (s "n") (s "y")) ∧
    (∀ (s : State), κ (s "n") (s "x") (s "y") → κ_1 (s "n") (s "x") 0) ∧
      (∀ (s : State), κ_1 (s "n") (s "x") (s "y") → κ_2 (s "n") (s "x") (s "y")) ∧
        (∀ (s : State), κ_2 (s "n") (s "x") (s "y") ∧ (s "x" != 0) = true → κ_3 (s "n") (s "x" - 1) (s "y")) ∧
          (∀ (s : State), κ_3 (s "n") (s "x") (s "y") → κ_2 (s "n") (s "x") (s "y" + 1)) ∧
            ∀ (s : State), κ_2 (s "n") (s "x") (s "y") ∧ (s "x" != 0) = false → s "y" = s "n") :=
  by
  apply propext
  apply Iff.intro
  intro ⟨k, k1, k2, k3, _⟩
  exists k3, k2, k, k1
  intro ⟨k3, k2, k, k1, _⟩
  exists k, k1, k2, k3

theorem solve_head :
  (∃ (x x_1 : Int → Int → Int → Prop),
  (∀ (s : State), ∃ (y : 0 ≤ s "n" → State), ∀ (x : 0 ≤ s "n"), 0 ≤ y x "n" ∧ s "n" = y x "n" ∧ s "y" = y x "y") ∧
    (∀ (s x : State),
        ∃ (y y_1 : 0 ≤ x "n" → s "n" = x "n" → s "x" = x "n" → s "y" = x "y" → State),
          ∀ (x_2 : 0 ≤ x "n") (x_3 : s "n" = x "n") (x_4 : s "x" = x "n") (x : s "y" = x "y"),
            0 ≤ y_1 x_2 x_3 x_4 x "n" ∧
              y x_2 x_3 x_4 x "n" = y_1 x_2 x_3 x_4 x "n" ∧
                y x_2 x_3 x_4 x "x" = y_1 x_2 x_3 x_4 x "n" ∧
                  y x_2 x_3 x_4 x "y" = y_1 x_2 x_3 x_4 x "y" ∧
                    s "n" = y x_2 x_3 x_4 x "n" ∧ s "x" = y x_2 x_3 x_4 x "x") ∧
      (∀ (s x x_2 : State),
          0 ≤ x_2 "n" →
            x "n" = x_2 "n" →
              x "x" = x_2 "n" →
                x "y" = x_2 "y" → s "n" = x "n" → s "x" = x "x" → s "y" = 0 → x_1 (s "n") (s "x") (s "y")) ∧
        (∀ (s : State), x_1 (s "n") (s "x") (s "y") → ¬s "x" = 0 → x (s "n") (s "x" - 1) (s "y")) ∧
          (∀ (s : State), x (s "n") (s "x") (s "y") → x_1 (s "n") (s "x") (s "y" + 1)) ∧
            ∀ (s : State), x_1 (s "n") (s "x") (s "y") → s "x" = 0 → s "y" = s "n") =
  ∃ (x x_1 : Int → Int → Int → Prop),
  (∀ (s : State), True) ∧
    (∀ (s x : State), True) ∧
      (∀ (s x x_2 : State),
          0 ≤ x_2 "n" →
            x "n" = x_2 "n" →
              x "x" = x_2 "n" →
                x "y" = x_2 "y" → s "n" = x "n" → s "x" = x "x" → s "y" = 0 → x_1 (s "n") (s "x") (s "y")) ∧
        (∀ (s : State), x_1 (s "n") (s "x") (s "y") → ¬s "x" = 0 → x (s "n") (s "x" - 1) (s "y")) ∧
          (∀ (s : State), x (s "n") (s "x") (s "y") → x_1 (s "n") (s "x") (s "y" + 1)) ∧
            ∀ (s : State), x_1 (s "n") (s "x") (s "y") → s "x" = 0 → s "y" = s "n" := by
  apply propext ; apply Iff.intro
  · intro ⟨x, x1, ⟨h1, h2, h3, h4, h5, h6⟩⟩
    exists x, x1
    and_intros
    intros ; trivial
    intros ; trivial
    assumption
    assumption
    assumption
    assumption
  · intro ⟨x, x1, ⟨h1, h2, h3, h4, h5, h6⟩⟩
    exists x, x1
    and_intros
    · intro s ; exists fun _ => s
      simp
    · intro s x
      exists fun _ _ _ _ => s
      exists fun _ _ _ _ => s
      simp_all
    · assumption
    · assumption
    · assumption
    · assumption


-- κ = fun nv xv yv => xv + yv = nv ∧ 0 ≤ xv
theorem slowAssign_correct :
    ValidHoareTriple (fun s => 0 ≤ s "n") slowAssign (fun s => s "y" = s "n") := by
  apply whileCHC_sound ["n", "x", "y"]
  dsimp [whileCHC, slowAssign, State.update, applyNary]
  hoist_exists
  rw [flip_local_2]
  under_exists1 =>
    under_exists1 =>
      solve_fusion
  simp ; hoist_exists
  rw [solve_head]
  solve_fixpoint
