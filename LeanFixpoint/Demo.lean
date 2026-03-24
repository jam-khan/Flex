import Lean

import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Command

open Lean Elab Meta Command Tactic

theorem ex1Proof :
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  solve_fixpoint

def ex1Constraint : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

#translate_and_solve ex1Constraint

theorem ex2Proof :
  ∃ κx : Int → Prop, ∃ κy : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          (∀ ν : Int, ν = n → κx ν)
        ∧ (∀ ν : Int, ν = p → κy ν)
        ∧ (∀ ν : Int, κx ν → κy ν)
        ∧ (∀ y : Int, κy y →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ ν : Int, ν = n ∧ z = ν
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ p : Int, p = x + 1 ∧
    ((∃ ν : Int, ν = p ∧ z = ν) ∨ (∃ ν : Int, (∃ α : Int, α = n ∧ ν = α) ∧ z = ν))
  simp
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · assumption
  · exists x
    grind
  · intro _ x' _ _
    exists x'
    grind
  · grind

def ex2Constraint : Prop :=
  ∃ κx : Int → Prop, ∃ κy : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          (∀ ν : Int, ν = n → κx ν)
        ∧ (∀ ν : Int, ν = p → κy ν)
        ∧ (∀ ν : Int, κx ν → κy ν)
        ∧ (∀ y : Int, κy y →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

#translate_and_solve ex2Constraint

theorem ex3Proof :
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν) := by
  solve_fixpoint

def ex3Constraint : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν)

#translate_and_solve ex3Constraint
