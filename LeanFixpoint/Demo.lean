import Lean

import Aesop
import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Elab.ToExpr
import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Command

-- open Lean Elab Tactic Meta Grind in
-- elab "grindx" : tactic => do
--   let params : Grind.Params := {
--     config    := default
--     norm      := default
--     normProcs := #[]
--   }
--   -- Process ALL current goals, not just the first
--   let goals ← getGoals
--   for mvarId in goals do
--     let result ← GrindM.run (params := params) do
--       let goal ← mkGoal mvarId
--       let goal ← goal.internalizeAll
--       goal.grind
--     match result with
--     | GrindResult.closed   => pure ()
--     | GrindResult.failed _ => throwError "grindx: failed to close goal {mvarId}"
--   pruneSolvedGoals

-- Step 1: Get more and more complicated examples than just simple ones.
def ex1 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

theorem ex1Proof : ex1 := by
  solve_fixpoint

def ex2 : Prop :=
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
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

theorem ex2Proof : ex2 := by
  solve_fixpoint


def ex3 : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν)

#translate_and_solve ex3

theorem ex3Proof : ex3 := by
  solve_fixpoint


-- ex4: Three-step chain: inc → dec → inc
-- ex4 x = inc (dec (inc x))  =  x+1 ≥ 0
-- κ1 = almost-nat (0 ≤ ν-1), κ2 = nat (0 ≤ ν)
def ex4 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν)
    ∧ (∀ y : Int, κ1 y →
        ∀ ν : Int, ν = y - 1 → κ2 ν)
    ∧ (∀ z : Int, κ2 z →
        ∀ ν : Int, ν = z + 1 → 0 ≤ ν)

#translate_and_solve ex4

theorem ex4Proof : ex4 := by
  solve_fixpoint

-- ex5: Three-step chain: dec → inc → inc
-- ex5 x = inc (inc (dec x))  =  x+1 ≥ 0
-- κ1 = almost-nat (0 ≤ ν+1), κ2 = nat
def ex5 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ1 ν)
    ∧ (∀ y : Int, κ1 y →
        ∀ ν : Int, ν = y + 1 → κ2 ν)
    ∧ (∀ z : Int, κ2 z →
        ∀ ν : Int, ν = z + 1 → 0 ≤ ν)

#translate_and_solve ex5

theorem ex5Proof : ex5 := by
  solve_fixpoint

-- ex6: Two independent paths, each checked separately
-- ex6 x = (inc x, inc (dec x))  both outputs ≥ 0
-- κ1 for the `inc x` branch (trivially nat), κ2 = almost-nat for `dec x`
def ex6 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν)
    ∧ (∀ a : Int, κ1 a → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν)

#translate_and_solve ex6

theorem ex6Proof : ex6 := by
  solve_fixpoint

-- ex7: Diamond — two sources flow into one κ, then one consumer
-- ex7 x = let ys = [inc x, dec x] in inc (last ys)  ≥ 0
-- κ = almost-nat: both (x+1) and (x-1) satisfy 0 ≤ ν+1
def ex7 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ ν)
    ∧ (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

#translate_and_solve ex7

theorem ex7Proof : ex7 := by
  solve_fixpoint

-- ex8: Two Nat inputs, one intermediate binder
-- ex8 (x y : Nat) = let a = dec x in a + 1 + y  ≥ 0
-- κ = almost-nat; consumer uses both κ a and 0 ≤ y
def ex8 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ y : Int,
        0 ≤ y →
        (∀ ν : Int, ν = x - 1 → κ ν)
      ∧ (∀ a : Int, κ a →
          ∀ ν : Int, ν = a + 1 + y → 0 ≤ ν)

#translate_and_solve ex8

theorem ex8Proof : ex8 := by
  solve_fixpoint

-- ex9: Four-step chain: inc → dec → inc → dec
-- ex9 x = dec (inc (dec (inc x)))  =  x  ≥ 0
-- κ1=almost-nat, κ2=nat, κ3=almost-nat, final check 0 ≤ ν
def ex9 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop, ∃ κ3 : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν)
    ∧ (∀ a : Int, κ1 a →
        ∀ ν : Int, ν = a - 1 → κ2 ν)
    ∧ (∀ b : Int, κ2 b →
        ∀ ν : Int, ν = b + 1 → κ3 ν)
    ∧ (∀ c : Int, κ3 c →
        ∀ ν : Int, ν = c - 1 → 0 ≤ ν)

#translate_and_solve ex9

theorem ex9Proof : ex9 := by
  solve_fixpoint

-- ex10: Three-way merge into one κ, stronger consumer (needs inc inc)
-- ex10 x = let ys = [dec x, x, inc x] in inc (inc (last ys))  ≥ 0
-- κ = almost-nat: weakest common refinement is 0 ≤ ν+1 (from dec x)
-- consumer: 0 ≤ y+2, follows from 0 ≤ y+1
def ex10 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ ν : Int, ν = x     → κ ν)
    ∧ (∀ ν : Int, ν = x + 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 2 → 0 ≤ ν)

#translate_and_solve ex10

theorem ex10Proof : ex10 := by
  solve_fixpoint

-- ex11: Three-κ chain with multi-producer merge at κ2
-- Given 0 ≤ x, produce x into κ1. Then κ1 feeds two values (a-2) and (a+1)
-- both into κ2. κ2 feeds into κ3 via +2. κ3 must be ≥ 0.
-- κ1(z) = 0 ≤ z, κ2(z) = 0 ≤ z + 2 (weakest from a-2 path), κ3(z) = 0 ≤ z
def ex11 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop, ∃ κ3 : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x → κ1 ν)
    ∧ (∀ a : Int, κ1 a →
          (∀ ν : Int, ν = a - 2 → κ2 ν)
        ∧ (∀ ν : Int, ν = a + 1 → κ2 ν))
    ∧ (∀ b : Int, κ2 b →
        ∀ ν : Int, ν = b + 2 → κ3 ν)
    ∧ (∀ c : Int, κ3 c → 0 ≤ c)

#translate_and_solve ex11

theorem ex11Proof : ex11 := by
  solve_fixpoint

-- ex12: Four-κ diamond — two independent processing paths rejoin at κ3
-- Given 0 ≤ x:
--   Path 1: (x-1) → κ1, then κ1 → (+3) → κ3
--   Path 2: (x+1) → κ2, then κ2 → (-1) → κ3
-- κ3 feeds into κ4 via identity, κ4 must be ≥ 0.
-- κ1(z) = 0 ≤ z+1, κ2(z) = 0 ≤ z-1
-- Path 1 into κ3: z = a+3 where 0≤a+1 → z ≥ 2
-- Path 2 into κ3: z = b-1 where 0≤b-1 → z ≥ 0
-- κ3(z) = 0 ≤ z (disjunction, weaker path dominates)
-- κ4(z) = 0 ≤ z
def ex12 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
  ∃ κ3 : Int → Prop, ∃ κ4 : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ1 ν)
    ∧ (∀ ν : Int, ν = x + 1 → κ2 ν)
    ∧ (∀ a : Int, κ1 a →
        ∀ ν : Int, ν = a + 3 → κ3 ν)
    ∧ (∀ b : Int, κ2 b →
        ∀ ν : Int, ν = b - 1 → κ3 ν)
    ∧ (∀ c : Int, κ3 c →
        ∀ ν : Int, ν = c → κ4 ν)
    ∧ (∀ d : Int, κ4 d → 0 ≤ d)

#translate_and_solve ex12

theorem ex12Proof : ex12 := by
  solve_fixpoint
