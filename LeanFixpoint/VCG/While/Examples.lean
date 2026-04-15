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
    body := assign "x" (fun _ => 5) (fun s => s "x" = 5) }

theorem assign_correct : dec_assign.outerTriple := by
  apply verification_correct
  intro s _; simp [State.update]

/-! ## Example 3: Sequence — {{ True }} x := 5; y := x + 1 {{ y = 6 }} -/

def dec_seq : Decorated :=
  { pre  := fun _ => True
    body := seq
      (assign "x" (fun _ => 5) (fun s => s "x" = 5))
      (assign "y" (fun s => s "x" + 1) (fun s => s "y" = 6)) }

theorem seq_correct : dec_seq.outerTriple := by
  apply verification_correct
  constructor
  · intro s _; simp [State.update]
  · intro s hx; simp [DCom.postQ] at hx; simp [State.update, hx]

/-! ## Example 4: While loop (reduce to zero)
    {{ True }} while x ≠ 0 do x := x - 1 end {{ x = 0 }}
    Loop invariant: True
-/

def dec_while : Decorated :=
  { pre  := fun _ => True
    body := cwhile (fun s => s "x" != 0)
      (fun _ => True)
      (assign "x" (fun s => s "x" - 1) (fun _ => True))
      (fun s => s "x" = 0) }

-- See the VCs in proof state:
example : dec_while.outerTriple := by
  apply verification_correct
  dsimp [Decorated.vconds, dec_while, vcond, assertImplies, DCom.postQ]
  -- Goal:
  --   (∀ s, True → True)
  -- ∧ (∀ s, True ∧ (s "x" != 0) = true → True)
  -- ∧ (∀ s, True → True)
  -- ∧ (∀ s, True ∧ (s "x" != 0) = false → s "x" = 0)
  sorry

theorem while_correct : dec_while.outerTriple := by
  apply verification_correct
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro s ⟨_, hg⟩; simp at hg; omega

/-! ## Example 5: While with nontrivial invariant
    {{ 0 ≤ n }}
    x := n; y := 0;
    while x ≠ 0 do x := x - 1; y := y + 1 end
    {{ y = n }}
    Invariant: x + y = n ∧ 0 ≤ x
-/

def Inv_slow : Assertion := fun s => s "x" + s "y" = s "n" ∧ 0 ≤ s "x"

def dec_slow : Decorated :=
  { pre  := fun s => 0 ≤ s "n"
    body := seq
      (assign "x" (fun s => s "n") (fun s => s "x" = s "n" ∧ 0 ≤ s "x"))
      (seq
        (assign "y" (fun _ => 0) Inv_slow)
        (cwhile (fun s => s "x" != 0)
          (fun s => s "x" + s "y" = s "n" ∧ 0 ≤ s "x" ∧ s "x" ≠ 0)
          (seq
            (assign "x" (fun s => s "x" - 1)
              (fun s => s "x" + (s "y" + 1) = s "n" ∧ 0 ≤ s "x"))
            (assign "y" (fun s => s "y" + 1) Inv_slow))
          (fun s => s "y" = s "n"))) }

theorem slow_correct : dec_slow.outerTriple := by
  apply verification_correct
  dsimp [Decorated.vconds, dec_slow, vcond, assertImplies, DCom.postQ,
        Inv_slow, State.update]
  solve_fixpoint
