import LeanFixpoint.VCG.While.Hoare
import LeanFixpoint.VCG.While.Tactics
import LeanFixpoint.Tactic

/-! # Constrained Horn Clause Generation

  `whileCHC readOnlyVars inScope pre c post` produces a Lean Prop that is a system of
  Constrained Horn Clauses.  `readOnlyVars` are fixed variables available throughout (e.g.,
  loop bounds, input parameters).  `inScope` tracks currently available variables,
  expanding dynamically as new variables are assigned within the command.

  Every existential — both `seq` midpoints and `cwhile` invariants — has type
  `NaryProp inScope.length` (or a derived scope), yielding one argument per variable
  currently in scope.  The result is directly solvable by `solve_fixpoint`.

  Soundness: if the CHC system is satisfiable, then `ValidHoareTriple pre c post`.
-/

/-- Generate CHCs for a command with dynamic variable scoping.
    `readOnlyVars` are always-available variables (e.g., loop bounds).
    `inScope` is the current scope (readOnlyVars + any assigned variables so far).
    As the command executes:
    - `.seq c₁ c₂`: scope expands after c₁ (c₂ sees c₁'s assignments)
    - `.ite`: branches stay isolated (no escape of assigned variables)
    - `.cwhile`: loop body can assign locally; invariant stays at pre-loop scope -/
@[simp]
def whileCHC (readOnlyVars : List CVar) (inScope : List CVar)
    (pre : Assertion) (c : Cmd) (post : Assertion) : Prop :=
  match c with
  | .skip =>
    ∀ s, pre s → post s

  | .assign x f =>
    ∀ s, pre s → post (s[x ↦ f s])

  | .seq c₁ c₂ =>
    let midScope := (inScope ++ c₁.assignedVars).eraseDups
    ∃ κ : NaryProp midScope.length,
      whileCHC readOnlyVars inScope pre c₁ (applyNary midScope κ) ∧
      whileCHC readOnlyVars midScope (applyNary midScope κ) c₂ post

  | .ite g c₁ c₂ =>
    whileCHC readOnlyVars inScope (fun s => pre s ∧ g s = true) c₁ post
    ∧ whileCHC readOnlyVars inScope (fun s => pre s ∧ g s = false) c₂ post

  | .cwhile g body =>
    let bodyScope := (inScope ++ body.assignedVars).eraseDups
    ∃ κ : NaryProp inScope.length,
      (∀ s, pre s → applyNary inScope κ s)                                                   -- init
    ∧ whileCHC readOnlyVars bodyScope (fun s => applyNary inScope κ s ∧ g s = true) body (applyNary inScope κ)    -- preserve
    ∧ (∀ s, applyNary inScope κ s ∧ g s = false → post s)                                    -- exit

/-- Soundness: if the CHC system is satisfiable, the Hoare triple holds. -/
@[simp]
theorem whileCHC_sound (readOnlyVars : List CVar) (inScope : List CVar)
    (pre : Assertion) (c : Cmd) (post : Assertion) :
    whileCHC readOnlyVars inScope pre c post → ValidHoareTriple pre c post := by
  induction c generalizing readOnlyVars inScope pre post with
  | skip =>
    intro h s₁ s₂ heval hpre
    cases heval; exact h _ hpre
  | assign x f =>
    intro h s₁ s₂ heval hpre
    cases heval; exact h _ hpre
  | seq c₁ c₂ ih₁ ih₂ =>
    intro ⟨κ, h₁, h₂⟩
    let midScope := (inScope ++ c₁.assignedVars).eraseDups
    exact hoare_seq (ih₁ readOnlyVars inScope _ _ h₁) (ih₂ readOnlyVars midScope _ _ h₂)
  | ite g c₁ c₂ ih₁ ih₂ =>
    intro ⟨h₁, h₂⟩
    exact hoare_if (ih₁ readOnlyVars inScope _ _ h₁) (ih₂ readOnlyVars inScope _ _ h₂)
  | cwhile g body ih =>
    intro ⟨κ, hinit, hpres, hpost⟩
    let bodyScope := (inScope ++ body.assignedVars).eraseDups
    exact hoare_while hinit (ih readOnlyVars bodyScope _ _ hpres) hpost

/-! # Examples -/

-- Program: x := 0; while x < n do x := x + 1 end
-- Pre: 0 ≤ n, Post: x = n
def countToN : Cmd :=
  .seq (.assign "x" (fun _ => 0))
       (.cwhile (fun s => decide (s "x" < s "n"))
                (.assign "x" (fun s => s "x" + 1)))

@[qualif] def Le (i1 i2 : Int) : Prop := i1 ≤ i2

-- vars=["n","x"]: inScope expands from ["n"] to ["n","x"] after first assignment
example : ValidHoareTriple (fun s => 0 ≤ s "n") countToN (fun s => s "x" = s "n") := by
  apply whileCHC_sound ["n"] ["n"]
  dsimp [whileCHC, countToN, State.update, applyNary, Cmd.assignedVars]
  simp_scopes ; simp
  hoist_exists
  solve_fixpoint

-- Program: while x ≠ 0 do x := x - 1 end
-- Pre: True, Post: x = 0
@[simp]
def reduceToZero : Cmd :=
  .cwhile (fun s => s "x" != 0)
          (.assign "x" (fun s => s "x" - 1))

set_option maxHeartbeats 1600000 in
-- x is pre-existing variable (in readOnlyVars); inScope stays ["x"]
theorem reduceToZero_correct :
    ValidHoareTriple (fun _ => True) reduceToZero (fun s => s "x" = 0) := by
  apply whileCHC_sound ["x"] ["x"]
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

-- κ = fun nv xv yv => xv + yv = nv ∧ 0 ≤ xv
theorem slowAssign_correct :
    ValidHoareTriple (fun s => 0 ≤ s "n") slowAssign (fun s => s "y" = s "n") := by
  apply whileCHC_sound ["n"] ["n"]
  dsimp [whileCHC, slowAssign, State.update, applyNary, Cmd.assignedVars]
  simp_scopes ; simp
  hoist_exists
  solve_fixpoint
