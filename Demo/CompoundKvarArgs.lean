import LeanFixpoint

/-
  Test: compound expressions as kvar arguments
  This exercises the List Expr kvar arg path (not just plain fvars).
-/

-- Test 1: Arithmetic expression as kvar arg: κ(x + 1) instead of κ(ν) where ν = x + 1
-- Equivalent to ex1 but with the binding inlined
def compoundArg1 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      κ (x - 1)
    ∧ (∀ y : Int, κ y → 0 ≤ y + 1)

theorem compoundArg1Proof : compoundArg1 := by
  solve_fixpoint

-- Test 2: Structure field projection as kvar arg
structure Pair where
  fst : Int
  snd : Int

def compoundArg2 : Prop :=
  ∃ κ : Int → Prop,
    ∀ p : Pair, 0 ≤ p.fst →
      κ p.fst
    ∧ (∀ v : Int, κ v → 0 ≤ v)

theorem compoundArg2Proof : compoundArg2 := by
  solve_fixpoint

-- Test 3: Two kvars with struct field args and cross-flow
def compoundArg3 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ p : Pair, 0 ≤ p.fst → 0 ≤ p.snd →
      κ1 p.fst
    ∧ κ2 p.snd
    ∧ (∀ v : Int, κ1 v → 0 ≤ v)
    ∧ (∀ v : Int, κ2 v → 0 ≤ v)

theorem compoundArg3Proof : compoundArg3 := by
  solve_fixpoint

-- Test 4: Arithmetic on field projection as kvar arg
def compoundArg4 : Prop :=
  ∃ κ : Int → Prop,
    ∀ p : Pair, 0 ≤ p.fst →
      κ (p.fst + 1)
    ∧ (∀ v : Int, κ v → 0 ≤ v)

theorem compoundArg4Proof : compoundArg4 := by
  solve_fixpoint
