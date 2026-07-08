import Flex

/-!
  # Demo — `pa_cert`, the certifying Predicate Abstraction tactic (paper §5)

  `pa_cert` solves a cut-only constraint `∃κ̄. c` by weakening to the greatest
  inductive fixpoint and then EMITTING the §5 `bridge` proof term: each cyclic
  κ-head is discharged by an `And.intro` over per-survivor oracle proofs, which
  the Lean kernel re-checks. It then LEAVES the κ-free residual `c′` as goals,
  so each proof closes the residual queries afterwards (here with `grind`).

  Contrast `solve_fixpoint`, which throws the whole residual at `grind` without
  building a structured certificate for the κ-heads.
-/

-- ─── cyc0: simplest cyclic κ — single self-loop, no acyclic κ ──────────────
-- Seeded from x (0 ≤ x), loop decrements by 1, check 0 ≤ result.
-- Expected invariant: κ[ν, x] ↦ 0 ≤ ν   (from `pc_gez` at slot 0).
@[qualif] def pc_gez (v : Int)   : Prop := 0 ≤ v
@[qualif] def pc_le  (a b : Int) : Prop := a ≤ b

def cyc0 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κ ν x)                                  -- seed
    ∧ (∀ i : Int, κ i x ∧ 1 ≤ i → ∀ ν : Int, ν = i - 1 → κ ν x)  -- loop (cyclic)
    ∧ (∀ i : Int, κ i x → 0 ≤ i)                                  -- check

theorem cyc0_pa_cert : cyc0 := by
  pa_cert
  all_goals grind

-- ─── fibFastVC: the paper's flagship — cyclic κ with `fib` in the contract ──
-- The contract requires the return value to equal `fib n`, where `fib` is an
-- ordinary Lean def. The loop invariant
--   κ[i, prev, curr, n] ↦ prev = fib (i-1) ∧ curr = fib i ∧ i ≤ n
-- needs the `fib`-valued qualifiers below — beyond an SMT backend, but fine for
-- a Lean oracle (`grind` unfolds the `@[grind]`-tagged `fib_spec`).
@[grind]
def fib_spec (n : Int) : Int :=
  if n ≤ 1 then 1
  else fib_spec (n - 1) + fib_spec (n - 2)
  termination_by n.toNat

@[qualif] def pc_gt_one      (v : Int)   : Prop := v > 1
@[qualif] def pc_eq_fib      (v i : Int) : Prop := v = fib_spec i
@[qualif] def pc_eq_fib_pred (v i : Int) : Prop := v = fib_spec (i - 1)

def fibFastVC : Prop :=
  ∃ k : Int → Int → Int → Int → Prop,
    ∀ n : Int, n ≥ 0 →
      ((¬ (n ≤ 1)) →
        k 2 1 2 n
      ∧ (∀ i prev curr : Int,
          k i prev curr n →
            ((¬ (i < n)) → curr = fib_spec n)
          ∧ ((i < n) → k (i + 1) curr (prev + curr) n)))
    ∧ ((n ≤ 1) → 1 = fib_spec n)

theorem fibFastVC_pa_cert : fibFastVC := by
  pa_cert
  all_goals grind

#print axioms cyc0_pa_cert
#print axioms fibFastVC_pa_cert
