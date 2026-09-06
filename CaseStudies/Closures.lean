import Flex

/-!
  # Case study 4 — closures, contravariance, and the ladder's boundary

  A closure bound with `let`, passed to a user-defined higher-order function.
  This is the Fig. 1 `dot` shape, and the file locates *exactly* where the
  discharge ladder stops and a `generate`-style VC generator must begin.

  Findings (each pinned by a test below):
  1. `sumRange.spec` — an arrow-refined binder — passes on rung 2; the
     contravariant hypothesis rides the induction motive.
  2. `plusOnes.spec` passes on rung 1: grind's E-matching instantiates
     `sumRange.spec` via its `grind_pattern` and discharges the contravariant
     ∀-antecedent by skolemizing its negation down to arithmetic. Search
     handles instantiating specs that *exist*.
  3. The boundary is a consequence no registered spec states: proving
     `0 < n → 0 < plusOnes n` needs `g`'s template type
     `(j | κ₁ j) => (r | κ₂ r j)` instantiated at κ₂ := (1 ≤ ·) — a *fresh
     instance* of sumRange's spec. E-matching has nothing to match; all three
     rungs fail (`fail_if_success` below).
  4. Once that instance is proved and registered, the identical ladder call
     succeeds. So `generate`'s job is not discharging contravariance — search
     does that — it is synthesizing and registering fresh κ-instances of
     template specs.

  Zeta caveat for `generate`: on the search path the `let`-bound `g` is
  reduced away before anything types it. The κ's of `g`'s template exist only
  while `g` is a binder, so a checker must intercept the body before zeta.
-/

def sumRange (lo hi : Int) (f : Int → Int) : Int :=
  if hi ≤ lo then 0 else f lo + sumRange (lo + 1) hi f
  termination_by (hi - lo).toNat
  decreasing_by omega

-- Arrow-refined binder: f's hypothesis is the arrow denotation
-- ∀ i, lo ≤ i ∧ i < hi → 0 ≤ f i. Discharged by rung 2 (fun_induction);
-- the hypothesis is reverted into the motive, so each case sees it at the
-- right lo.
#spec sumRange (lo : Int) (hi : Int)
  (f : (i : Int | lo ≤ i ∧ i < hi) => (r : Int | 0 ≤ r)) => (r : Int | 0 ≤ r)

def plusOnes (n : Int) : Int :=
  let g := fun j => j + 1
  sumRange 0 n g

-- Rung 1: grind instantiates sumRange.spec at (0, n, g) through its pattern
-- and proves the contravariant clause ∀ i, 0 ≤ i ∧ i < n → 0 ≤ g i by
-- skolemization + cutsat. g never needs a type here — it is zeta-reduced.
#spec plusOnes (n : Int) => (r : Int | 0 ≤ r)

-- ───────────────────────────────────────────────────────────────────────────
-- The boundary, and generate's job description
-- ───────────────────────────────────────────────────────────────────────────

-- The κ₂ := (1 ≤ ·) instance of sumRange's template spec. A generate-style
-- VC generator would emit statement, proof, and registration from the #spec
-- template; today all three are by hand.
theorem sumRange.spec_pos : ∀ (lo hi : Int) (f : Int → Int),
    (∀ i, lo ≤ i ∧ i < hi → 1 ≤ f i) → lo < hi → 1 ≤ sumRange lo hi f := by
  intro lo hi f
  fun_induction sumRange <;> grind

-- Not registered yet — first, pin that the ladder fails without it. The
-- statement is true and its witness follows, but no rung can find it: rung 1
-- has no pattern to match, rung 2 has no recursion to induct on, rung 3 has
-- no foldl.
theorem plusOnes.spec_pos : ∀ n : Int, 0 < n → 0 < plusOnes n := by
  fail_if_success flex_spec_solve plusOnes
  -- The witness generate must synthesize: the fresh instance above, plus the
  -- call-site contravariance clause κ₁ ⊑ dom(g) (here: 1 ≤ j + 1).
  intro n hn
  show 0 < sumRange 0 n (fun j => j + 1)
  have h := sumRange.spec_pos 0 n (fun j => j + 1) (fun i _ => by grind) hn
  omega

-- Registration — the step generate automates:
grind_pattern sumRange.spec_pos => sumRange lo hi f

-- The identical ladder call that failed above now succeeds.
example : ∀ n : Int, 0 < n → 0 < plusOnes n := by
  flex_spec_solve plusOnes

#print sumRange.spec
#print axioms sumRange.spec
#print axioms plusOnes.spec
#print axioms plusOnes.spec_pos
