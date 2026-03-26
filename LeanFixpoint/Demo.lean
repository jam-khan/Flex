import Lean

import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Command

open Lean Elab Meta Command Tactic

theorem ex1Proof :
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  solve_fixpoint
  intro x hx
  dsimp only
  refine ⟨?_, ?_⟩
  -- Conjunct 1 (HEAD: κ in head)
  -- goal: sol_κ(ν) = ∃ x, 0 ≤ x ∧ ∃ ν₁, ν₁ = x - 1 ∧ ν = ν₁
  · intro v hv
    exists x
    constructor
    · grind
    · exists v
  -- Conjunct 2 (BODY)
  · grind

def ex1Constraint : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

#translate_and_solve ex1Constraint

theorem ex2Proof :
  ∃ κx : Int → Prop, ∃ κy : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ n : Int,
        n = x - 1 →
        ∀ p : Int,
          p = x + 1 →
          (∀ ν : Int, ν = n → κx ν)
        ∧ (∀ ν : Int, ν = p → κy ν)
        ∧ (∀ ν : Int, κx ν → κy ν)
        ∧ (∀ y : Int, κy y →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  exists fun z => ∃ x, 0 ≤ x ∧ ∃ n, n = x - 1 ∧ ∃ p, p = x + 1 ∧ ∃ ν, ν = n ∧ z = ν
  exists fun z => ∃ x, 0 ≤ x ∧ ∃ n, n = x - 1 ∧ ∃ p, p = x + 1 ∧
      ((∃ ν, ν = p ∧ z = ν) ∨ ∃ ν, (∃ ν_α, ν_α = n ∧ ν = ν_α) ∧ z = ν)
  intro x hx n hn p hp
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exists x
    constructor
    · exact hx
    · exists n
      constructor
      · exact hn
      · exists p
        constructor
        · exact hp
        · exists v
  · intro v hv
    exists x
    constructor
    · exact hx
    · exists n
      constructor
      · exact hn
      · exists p
        constructor
        · exact hp
        · left
          exists v
  -- Conjunct 3 (HEAD: κy in head, κx in body, Or.inr)
  · intro ν hκx
    obtain ⟨x', hx', n', hn', p', hp', ν', hν', hν_eq⟩ := hκx
    exists x'
    constructor
    · exact hx'
    · exists n'
      constructor
      · exact hn'
      · exists p'
        constructor
        · exact hp'
        · right
          exists ν'
          constructor
          · exists ν'
          · exact hν_eq
  -- Conjunct 4 (BODY)
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
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Conjunct 1 (HEAD: κb in head, κa in body)
  -- hyp: sol_κa(a) = ∃ ν, 0 ≤ ν ∧ a = ν
  -- goal: sol_κb(ν) = ∃ a, (∃ ν, 0 ≤ ν ∧ a = ν) ∧ ∃ ν₁, ν₁ = a - 1 ∧ ν = ν₁
  · intro a ha ν hν
    obtain ⟨ν₀, hν₀, ha_eq⟩ := ha
    exists a
    constructor
    · exists ν₀
    · exists ν
  -- Conjunct 2 (HEAD: κc in head, κb in body)
  -- hyp: sol_κb(b) = ∃ a, (∃ ν, 0 ≤ ν ∧ a = ν) ∧ ∃ ν, ν = a - 1 ∧ b = ν
  -- goal: sol_κc(ν) = ∃ b, (∃ a, (∃ ν, 0 ≤ ν ∧ a = ν) ∧ ∃ ν, ν = a - 1 ∧ b = ν) ∧ ∃ ν₁, ν₁ = b + 1 ∧ ν = ν₁
  · intro b hb ν hν
    obtain ⟨a, ⟨ν₀, hν₀, ha_eq⟩, ν₁, hν₁, hb_eq⟩ := hb
    exists b
    constructor
    · exists a
      constructor
      · exists ν₀
      · exists ν₁
    · exists ν
  -- Conjunct 3 (HEAD: κa in head)
  -- goal: sol_κa(ν) = ∃ ν₁, 0 ≤ ν₁ ∧ ν = ν₁
  · intro v hv
    exists v
    grind
  -- Conjunct 4 (BODY)
  · grind



def ex3Constraint : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν)

#translate_and_solve ex3Constraint
