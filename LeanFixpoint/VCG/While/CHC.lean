import LeanFixpoint.VCG.While.Hoare
import LeanFixpoint.Tactic.Tactics
import LeanFixpoint.Tactic.SolveFusion

/-! # Constrained Horn Clause Generation

  `whileCHC pre c post` produces a Lean Prop that is a system of
  Constrained Horn Clauses. Each `cwhile` introduces an `∃ κ : State → Prop`
  as the unknown loop invariant. The result is directly solvable by `solve_fixpoint`.

  Soundness: if the CHC system is satisfiable, then `ValidHoareTriple pre c post`.
-/

/-- Generate CHCs for a command. The `pre` and `post` are the
    precondition and postcondition. Each `cwhile` introduces an
    existential `κ` representing the unknown loop invariant.

    The output is a Lean `Prop` with `∃ κ, (init) ∧ (preserve) ∧ (exit)`. -/
@[simp]
def whileCHC (pre : Assertion) (c : Cmd) (post : Assertion) : Prop :=
  match c with
  | .skip =>
    ∀ s, pre s → post s

  | .assign x f =>
    ∀ s, pre s → post (s[x ↦ f s])

  | .seq c₁ c₂ =>
    ∃ mid : Assertion, whileCHC pre c₁ mid ∧ whileCHC mid c₂ post

  | .ite g c₁ c₂ =>
    whileCHC (fun s => pre s ∧ g s = true) c₁ post
    ∧ whileCHC (fun s => pre s ∧ g s = false) c₂ post

  | .cwhile g body =>
    ∃ κ : Assertion,
      (∀ s, pre s → κ s)                                     -- init
    ∧ whileCHC (fun s => κ s ∧ g s = true) body κ             -- preserve
    ∧ (∀ s, κ s ∧ g s = false → post s)                       -- exit

/-- Soundness: if the CHC system is satisfiable, the Hoare triple holds. -/
@[simp]
theorem whileCHC_sound (pre : Assertion) (c : Cmd) (post : Assertion) :
    whileCHC pre c post → ValidHoareTriple pre c post := by
  induction c generalizing pre post with
  | skip =>
    intro h s₁ s₂ heval hpre
    cases heval; exact h _ hpre
  | assign x f =>
    intro h s₁ s₂ heval hpre
    cases heval; exact h _ hpre
  | seq c₁ c₂ ih₁ ih₂ =>
    intro ⟨mid, h₁, h₂⟩
    exact hoare_seq (ih₁ pre mid h₁) (ih₂ mid post h₂)
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

-- See the CHC system:
example : ValidHoareTriple (fun s => 0 ≤ s "n") countToN (fun s => s "x" = s "n") := by
  apply whileCHC_sound
  dsimp [whileCHC, countToN, State.update]
  hoist_exists
  exists fun s => s "x" ≤ s "n"
  exists fun s => s "x" ≤ s "n"
  simp
  solve_fusion

-- Program: while x ≠ 0 do x := x - 1 end
-- Pre: True, Post: x = 0
@[simp]
def reduceToZero : Cmd :=
  .cwhile (fun s => s "x" != 0)
          (.assign "x" (fun s => s "x" - 1))

set_option maxHeartbeats 1600000 in
-- Prove manually by providing κ:
theorem reduceToZero_correct :
    ValidHoareTriple (fun _ => True) reduceToZero (fun s => s "x" = 0) := by
  apply whileCHC_sound
  solve_fusion

-- Program: x := n; y := 0; while x ≠ 0 do x := x-1; y := y+1 end
-- Pre: 0 ≤ n, Post: y = n
-- κ will be: x + y = n ∧ 0 ≤ x
def slowAssign : Cmd :=
  .seq (.assign "x" (fun s => s "n"))
  (.seq (.assign "y" (fun _ => 0))
  (.cwhile (fun s => s "x" != 0)
    (.seq (.assign "x" (fun s => s "x" - 1))
          (.assign "y" (fun s => s "y" + 1)))))

-- Prove manually by providing κ:
theorem slowAssign_correct :
    ValidHoareTriple (fun s => 0 ≤ s "n") slowAssign (fun s => s "y" = s "n") := by
  apply whileCHC_sound
  dsimp [whileCHC, slowAssign, State.update]
  hoist_exists
  -- Provide mid for x := n
  exists fun s => s "x" = s "n" ∧ 0 ≤ s "n"
  exists fun s => s "x" + s "y" = s "n" ∧ 0 ≤ s "x"
  exists fun s => s "x" + s "y" = s "n" ∧ 0 ≤ s "x"
  exists fun s => s "x" + (s "y" + 1) = s "n" ∧ 0 ≤ s "x"
  solve_fusion
