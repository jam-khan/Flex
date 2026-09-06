import Flex

/-!
  # Case study 1 — first-order specs and modular composition

  The motivating example from the `#spec` design discussion, verbatim: a
  refinement spec over an *ordinary* Lean definition desugars into a theorem
  and is proved automatically, kernel-checked.

  The second half is the point of types over plain Floyd–Hoare: callers are
  verified against callee *specs*. Each `#spec` registers its theorem via
  `grind_pattern`, keyed on applications of the function — so `incTwice` and
  `maxAbs` verify without `inc`/`iabs`/`max3` ever being unfolded.
-/

-- ───────────────────────────────────────────────────────────────────────────
-- First-order specs
-- ───────────────────────────────────────────────────────────────────────────

def inc (x : Int) : Int := x + 1

#spec inc (x : Int | x > 0) => (result : Int | result > x)
-- generated + proved:  theorem inc.spec : ∀ (x : Int), x > 0 → inc x > x

def iabs (x : Int) : Int := if x < 0 then -x else x

#spec iabs (x : Int) => (r : Int | 0 ≤ r ∧ (r = x ∨ r = -x))

def max3 (a b c : Int) : Int := max a (max b c)

#spec max3 (a : Int) (b : Int) (c : Int) => (r : Int | a ≤ r ∧ b ≤ r ∧ c ≤ r)

-- ───────────────────────────────────────────────────────────────────────────
-- Modular composition: callees stay folded, their specs do the work
-- ───────────────────────────────────────────────────────────────────────────

def incTwice (x : Int) : Int := inc (inc x)

#spec incTwice (x : Int | x > 0) => (r : Int | r > x)   -- via inc.spec, twice

def maxAbs (x y : Int) : Int := max3 (iabs x) (iabs y) 0

#spec maxAbs (x : Int) (y : Int) => (r : Int | 0 ≤ r ∧ x ≤ r ∧ y ≤ r)
-- via iabs.spec (each argument is ≥ its input) and max3.spec (r bounds all)

#print inc.spec
#print axioms inc.spec
#print axioms incTwice.spec
#print axioms maxAbs.spec
