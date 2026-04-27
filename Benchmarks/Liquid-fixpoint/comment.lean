import LeanFixpoint
/-
  Liquid-fixpoint test: 6 κ-vars with cyclic dependencies.
  https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/comment.smt2

  Dependency classification:
    Cyclic (PA): k4 — self-loop via +1 step, plus k0↔k4, k4↔k5 cycles
    Acyclic (fusion): k0, k1, k2, k3, k5 (cycles through k4 get eliminated
                      by substituting their sols into k4's constraint)

  Existentials ordered acyclic-first, cyclic-last.

  Following Demo/Cyclic.lean `pa6` convention:
    - Outer scope vars appear as the LAST args of each κ.
    - The Bool branching var `a2` is NOT part of κ scope (only used for
      seed-branch guards at the outer `∀` level). Dropping it from κ
      signatures keeps the scope purely integer and lets PA find a clean
      `a0 ≤ first_arg` invariant for k4.

  Required invariant: `a0 ≤ first_arg` on k4.
-/

@[qualif] def q_eq_zero (v : Int)   : Prop := v = 0
@[qualif] def q_gt_zero (v : Int)   : Prop := 0 < v
@[qualif] def q_ge_zero (v : Int)   : Prop := 0 ≤ v
@[qualif] def q_lt_zero (v : Int)   : Prop := v < 0
@[qualif] def q_le_zero (v : Int)   : Prop := v ≤ 0
@[qualif] def q_eq      (a b : Int) : Prop := a = b
@[qualif] def q_gt      (a b : Int) : Prop := a > b
@[qualif] def q_ge      (a b : Int) : Prop := a ≥ b
@[qualif] def q_lt      (a b : Int) : Prop := a < b
@[qualif] def q_le      (a b : Int) : Prop := a ≤ b
@[qualif] def q_le1     (a b : Int) : Prop := a ≤ b - 1

def comment_vc : Prop :=
  -- acyclic first (per corrected SCC: only k1, k2, k3 are acyclic)
  ∃ k1 : Int → Int → Prop,
  ∃ k2 : Int → Int → Int → Prop,
  ∃ k3 : Int → Int → Int → Prop,
  -- cyclic last (k0, k4, k5 form one SCC via k0↔k4 and k4↔k5)
  ∃ k0 : Int → Int → Int → Prop,
  ∃ k5 : Int → Int → Int → Prop,
  ∃ k4 : Int → Int → Int → Prop,
    ∀ a0 : Int,
    ∀ a1 : Int,
    ∀ a2 : Bool,
      a0 < a1 →
        -- Branch: ¬a2
        (a2 = false →
            k0 a1 a0 a1
          ∧ k1 a0 a1
          ∧ k2 a0 a0 a1
          ∧ (∀ a3 : Int, k0 a3 a0 a1 → k3 a3 a0 a1)
          ∧ (∀ a4 : Int, k0 a4 a0 a1 → k4 a4 a0 a1)
          ∧ (∀ a5 : Int, k4 a5 a0 a1 → k0 a5 a0 a1))
      ∧ -- Branch: a2
        (a2 = true →
            k5 a0 a0 a1
          ∧ k1 a0 a1
          ∧ (∀ a6 : Int, k5 a6 a0 a1 → k2 a6 a0 a1)
          ∧ k3 a1 a0 a1
          ∧ (∀ a7 : Int, k5 a7 a0 a1 → k4 a7 a0 a1)
          ∧ (∀ a8 : Int, k4 a8 a0 a1 → k5 a8 a0 a1))
      ∧ -- Consumer (both branches)
        (k1 a0 a1 →
          ∀ a9 : Int, k4 a9 a0 a1 →
              (∀ a10 : Int, a10 = a9 + 1 → k4 a10 a0 a1)
            ∧ (∀ a11 : Int, k4 a11 a0 a1 →
                ∀ a12 : Int, k2 a12 a0 a1 →
                  ∀ a13 : Int, k3 a13 a0 a1 →
                    0 ≤ a11 - a0))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2000 in
theorem comment_proof : comment_vc := by
  -- solve_fixpoint

  -- dsimp only
  solve_fusion
  
  dsimp only
  -- solve_fusion

  sorry
