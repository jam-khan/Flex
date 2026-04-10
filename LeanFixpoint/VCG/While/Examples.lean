import LeanFixpoint.VCG.While.VCGen
import LeanFixpoint.Tactic.SolveFixpoint

open DCom

/-! ## Example 1: Skip — {{ True }} skip {{ True }} -/

def dec_skip : Decorated :=
  { pre  := fun _ => True
    body := skip (fun _ => True) }

theorem skip_correct : dec_skip.outerTriple := by
  apply verification_correct; intro _ _; trivial

/-! ## Example 2: Assignment — {{ True }} x := 5 {{ x = 5 }} -/

def dec_assign : Decorated :=
  { pre  := fun _ => True
    body := assign "x" (.lit 5) (fun s => s "x" = 5) }

theorem assign_correct : dec_assign.outerTriple := by
  apply verification_correct
  intro s _; simp [State.update, AExpr.eval]

/-! ## Example 3: Sequence — {{ True }} x := 5; y := x + 1 {{ y = 6 }} -/

def dec_seq : Decorated :=
  { pre  := fun _ => True
    body := seq
      (assign "x" (.lit 5) (fun s => s "x" = 5))
      (assign "y" (.add (.var "x") (.lit 1)) (fun s => s "y" = 6)) }

theorem seq_correct : dec_seq.outerTriple := by
  apply verification_correct
  constructor
  · intro s _; simp [State.update, AExpr.eval]
  · intro s hx
    simp [DCom.postQ] at hx
    simp [State.update, AExpr.eval, hx]

/-! ## Example 4: While loop (reduce to zero)
    {{ True }} while ¬(x = 0) do x := x - 1 end {{ x = 0 }}
    Loop invariant: True
-/

def dec_while : Decorated :=
  { pre  := fun _ => True
    body := cwhile
      (.not (.eq (.var "x") (.lit 0)))
      (fun _ => True)
      (assign "x" (.sub (.var "x") (.lit 1)) (fun _ => True))
      (fun s => s "x" = 0) }

theorem while_correct : dec_while.outerTriple := by
  apply verification_correct
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro s ⟨_, hg⟩
    simp [BExpr.eval, AExpr.eval] at hg
    omega

-- See the VCs in proof state:
example : dec_while.outerTriple := by
  apply verification_correct
  dsimp [Decorated.vconds, dec_while, vcond, assertImplies, DCom.postQ]

  solve_fixpoint

  -- Now check the proof state — it shows the 4 Horn clauses
  sorry
