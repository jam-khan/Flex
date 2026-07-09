import Lean
import Flex

/-!
# Memoized Fibonacci — one cyclic and one acyclic κ

Flux VC for a memoized `fib` (`fib_memo` with the memo invariant left inferred).
Two refinement variables:

* `κ_memo (k v)` — the memo-table invariant.  **Cyclic**: entry `n₀` is built
  from entries `n₀-1` and `n₀-2`, so `κ_memo` occurs in both body and head of the
  `set` clause.
* `κ_w (w n)` — the hit-branch intermediate `let w = *v`.  **Acyclic**, but its
  strongest solution is `∃ w', κ_memo n w' ∧ w = w'` (≈ `κ_memo n w`), i.e. it
  literally mentions the cyclic `κ_memo`.

This is the acyclic-σ̂-contains-cyclic-κ case: `solve_fixpoint` fuses `κ_w` away
(its solution carrying the `κ_memo` mvar), then predicate abstraction synthesizes
`κ_memo` from the qualifier bank and assigns that mvar, closing the goal.
-/

@[grind]
def fib_spec_fib (n : Int) : Int :=
  if n <= 1 then 1
  else fib_spec_fib (n - 1) + fib_spec_fib (n - 2)
  termination_by n.toNat

def FibMemoBoth :=
  ∃ κ_memo : (k v : Int) → Prop,       -- memo-table invariant            (cyclic)
  ∃ κ_w    : (w n : Int) → Prop,       -- hit-branch intermediate `let w` (acyclic)
   ∀ n₀ : Int, n₀ ≥ 0 →
       -- set: entry n₀ built from entries n₀-1, n₀-2   (κ_memo in body AND head → cyclic)
       (¬(n₀ ≤ 1) →
          ∀ a : Int, κ_memo (n₀ - 1) a →
          ∀ b : Int, κ_memo (n₀ - 2) b →
            κ_memo n₀ (a + b))
       -- hit: looked-up value satisfies κ_memo, bound to w   (κ_w def; κ_memo a guard)
     ∧ (∀ w : Int, κ_memo n₀ w → κ_w w n₀)
       -- result of the hit branch must be fib n₀            (κ_w use)
     ∧ (∀ w : Int, κ_w w n₀ → w = fib_spec_fib n₀)
       -- base branch returns 1
     ∧ (n₀ ≤ 1 → 1 = fib_spec_fib n₀)

-- Qualifiers scraped from the program text.
@[qualif] def q_eq_fib      (v i : Int) : Prop := v = fib_spec_fib i        -- from `-> usize[spec_fib(n)]`
@[qualif] def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)  -- from `spec_fib(n - 1)`
@[qualif] def q_le_one      (v   : Int) : Prop := v ≤ 1                     -- from `n <= 1`
@[qualif] def q_eq_one      (v   : Int) : Prop := v = 1                     -- from base value `1`
@[qualif] def q_le          (a b : Int) : Prop := a ≤ b                     -- from `i < n`, `n <= 1`
@[qualif] def q_ge_zero     (v   : Int) : Prop := 0 ≤ v                     -- from `usize` (≥ 0)

theorem FibMemoBoth_proof : FibMemoBoth := by
  solve_fixpoint
