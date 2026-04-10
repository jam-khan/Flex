import LeanFixpoint

/-
  Advanced compound kvar arg tests:
  - Multi-field ADT projections flowing through kvar chains
  - Nested struct access
  - Function application as kvar args

  NOTE: Tests with struct-typed binders and multiple guards
  (e.g., `∀ p : Point, 0 ≤ p.x → 0 ≤ p.y → ...`) currently fail
  because `reduce` unfolds struct projections in guards, producing
  expressions that the constraint extractor can't reassemble cleanly.
  Single-guard struct tests work fine.
-/

structure Point where
  x : Int
  y : Int

-- Test 1: Two-kvar chain with struct fields — single guard works
def adtChainSingle : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ p : Point, 0 ≤ p.x →
      (κ1 p.x)
    ∧ (∀ a : Int, κ1 a → κ2 (a + 1))
    ∧ (∀ a : Int, κ2 a → 1 ≤ a)

theorem adtChainSingleProof : adtChainSingle := by
  solve_fixpoint

-- Test 2: Two-kvar chain with struct fields — two guards (known limitation)
def adtChain : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ p : Point, 0 ≤ p.x → 0 ≤ p.y →
      (κ1 p.x p.y)
    ∧ (∀ a b : Int, κ1 a b → κ2 (a + 1) (b - 1))
    ∧ (∀ a b : Int, κ2 a b → 1 ≤ a)

-- TODO: fails due to reduce + struct guard interaction
theorem adtChainProof : adtChain := by
  sorry

-- Test 3: Uninterpreted function as kvar arg
def withFunction : Prop :=
  ∀ f : Int → Int,
    (∀ n : Int, 0 ≤ n → 0 ≤ f n) →
    ∃ κ : Int → Prop,
      ∀ x : Int, 0 ≤ x →
        (κ (f x))
      ∧ (∀ v : Int, κ v → 0 ≤ v)

theorem withFunctionProof : withFunction := by
  solve_fixpoint
