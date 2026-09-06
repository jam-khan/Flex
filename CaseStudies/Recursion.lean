import Flex

/-!
  # Case study 2 — recursive definitions

  `#spec` on a recursive definition is discharged by functional induction
  (`fun_induction`, rung 2 of the ladder): the conjunction in the result
  refinement *is* the inductive invariant, and it rides the induction motive.

  `sumToPlus` then composes against the *recursive* callee's spec — `sumTo`
  stays folded; only `sumTo.spec` is used.

  The file closes with the roadmap exhibit: the CHC that a future
  `fun_induction`→CHC VC generator would emit for `sumTo`, in the exact shape
  of `Benchmarks/Liquid-fixpoint/sum_rec-ok.lean`. There the invariant κ is
  *not* written by anyone — `fix` infers it from the `@[qualif]` bank. Today
  this CHC is written by hand; generating it from the `fun_induction` cases is
  the next step for this frontend.
-/

def sumTo (n : Int) : Int :=
  if n ≤ 0 then 0 else n + sumTo (n - 1)
  termination_by n.toNat
  decreasing_by omega

-- Rung 2: fun_induction sumTo <;> leafClosers; the conjunction rides the
-- motive. (Verified: each conjunct here also closes alone — the 0 < n guard
-- makes the IH n - 1 ≤ sumTo (n - 1) imply 0 ≤ sumTo (n - 1). For where the
-- ladder genuinely stops, see Closures.lean.)
#spec sumTo (n : Int) => (r : Int | 0 ≤ r ∧ n ≤ r)

-- Composition against a recursive callee: sumTo never unfolds.
def sumToPlus (n : Int) : Int := sumTo n + 1

#spec sumToPlus (n : Int) => (r : Int | 0 < r ∧ n < r)

-- ───────────────────────────────────────────────────────────────────────────
-- Roadmap exhibit: the CHC a VC generator would emit for sumTo's `0 ≤ r`.
-- κ is the summary of sumTo; `fix` INFERS κ := (0 ≤ ·) from the bank.
-- ───────────────────────────────────────────────────────────────────────────

@[qualif] def qr_ge_zero (v : Int) : Prop := 0 ≤ v

theorem sumTo_chc :
    ∃ κ : Int → Prop,
      (∀ n : Int, n ≤ 0 → ∀ v : Int, v = 0 → κ v)          -- base case
    ∧ (∀ n : Int, 0 < n → ∀ t : Int, κ t →
        ∀ v : Int, v = n + t → κ v)                         -- recursive case
    ∧ (∀ r : Int, κ r → 0 ≤ r) := by                        -- check clause
  fix

#print axioms sumTo.spec
#print axioms sumToPlus.spec
#print axioms sumTo_chc
