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
    ∀ x : Int,        -- {0} intro x
      0 ≤ x →         -- {1} intro hx
      ∀ n : Int,      -- {2} intro n
        n = x - 1 →   -- {3} intro hn
        ∀ p : Int,    -- {4} intro p
          p = x + 1 → -- {5} intro hp
        -- {6} constructor
        (
          -- {7}
          (∀ ν : Int, ν = n → κx ν)
        ∧ (∀ ν : Int, ν = p → κy ν)
        ∧ (∀ ν : Int, κx ν → κy ν)
        ∧ (∀ y : Int, κy y →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
        ) := by
  solve_fixpoint <;> try assumption <;> try grind


  sorry
  -- intro x hx
  -- refine ⟨?_, ?_, ?_, ?_⟩
  -- · grind
  -- · exists x
  --   grind
  -- · intro v x hx hv
  --   exists x
  --   grind
  -- · grind
  -- intro x
  -- intro hx
  -- intro n
  -- intro hn
  -- intro p
  -- intro hp
  -- constructor
  -- · intro v
  --   intro h
  --   exists x
  --   constructor
  --   · grind
  --   · exists n
  --     constructor
  --     · grind
  --     · exists p
  --       sorry
  -- · constructor
  --   . intro v
  --     intro h
  --     exists x
  --     constructor
  --     · sorry
  --     · sorry
  --   · constructor
  --     · intro v
  --       intro hp
  --       have ⟨x1, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hp
  --       exists x1
  --       constructor
  --       · grind
  --       ·
  --         exists n
  --         constructor
  --         · simp
  --           grind
  --         · exists p
  --           constructor
  --           · grind
  --           · left
  --             exists x
  --             grind

  --         sorry
  --     · sorry
  --     intro h
  --     have ⟨x, _⟩ := h
  --     exists x
  --     -- no existential inside? `grind`
  --     grind

  -- · intro v hv
  --   exists x
  --   grind
  -- · constructor
  --   · intro v hv
  --     exists x
  --     grind
    -- · constructor
    --   · intro v hv
    --     exists x
    --     constructor
    --     · grind
    --     · exists x
    --       constructor
    --       ·

    --       grind
    --   · grind


  --   -- have ⟨x, h⟩ := hv
  --   try exists x <;> grind

  -- · sorry
  -- · sorry
  -- · sorry
  -- refine ⟨?_, ?_, ?_⟩
  -- · try exists x <;> grind
  -- · intro v x' hx' hv
  --   try exists x' <;> grind
  -- · grind

-- c₁ ∧ c₂ ∧ (...) ∧ cₙ
-- tactic: refine and enter each
-- ∀ (x: Int) => P(x)
-- tactic: intro x
-- ∃ (x: Int) p ∧ (P(x))
-- tactic: forall var in hypothesis, try exists var <;> grind
-- (∃ y, P(y)) → Q
-- tactic: intro h; have <x', _> := h

  -- exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ ν : Int, ν = n ∧ z = ν
  -- exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ p : Int, p = x + 1 ∧
  --   ((∃ ν : Int, ν = p ∧ z = ν) ∨ (∃ ν : Int, (∃ α : Int, α = n ∧ ν = α) ∧ z = ν))
  -- simp
  -- intro x hx
  -- refine ⟨?_, ?_, ?_, ?_⟩
  -- · assumption
  -- · exists x
  --   grind
  -- · intro v x' hx' hv
  --   exists x'
  --   grind
  -- · grind
  -- intro x hx n hn p hp
  -- refine ⟨?_, ?_, ?_, ?_⟩
  -- · intro ν hν
  --   exists x
  --   grind
  -- · intro ν hν
  --   exists x
  --   grind
  -- · intro v hkx
  --   obtain ⟨x', _⟩ := hkx
  --   exists x'
  --   simp <;> grind
  -- · intro y h
  --   obtain ⟨x', _⟩ := h
  --   grind

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
