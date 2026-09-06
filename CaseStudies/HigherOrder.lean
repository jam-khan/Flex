import Flex

/-!
  # Case study 3 — higher-order folds with κ-inferred invariants

  The flagship demo: `#spec` on definitions built from `List.foldl`, where the
  accumulator invariant is **inferred**, not written. Rung 3 of the ladder
  rewrites the goal via `foldl_inv_spec`, whose hypothesis is an
  `∃ inv : β → Prop, …` in CHC clause shape — `inv` is a κ, and `fix`
  (certifying predicate abstraction) solves it from the `@[qualif]` bank,
  emitting a bridge term the kernel re-checks.

  For `sumPos` the inferred invariant is `0 ≤ acc`. Nothing in the source or
  the spec mentions it. This is the case that plain `grind` cannot do (no
  generalization over the accumulator), and where `mvcgen`-style verification
  would ask the user to write the invariant.

  `sumAll` adds a refined *binder*: the precondition on the list's elements
  reaches predicate abstraction's oracle through the local context, so the
  same bank suffices.
-/

-- The qualifier bank: atoms PA may conjoin per κ. The user states *candidate
-- facts*, never which κ they solve or how they combine.
@[qualif] def qh_ge_zero (v : Int) : Prop := 0 ≤ v

def sumPos (xs : List Int) : Int :=
  xs.foldl (fun acc a => if 0 < a then acc + a else acc) 0

-- Rung 3: unfold; apply foldl_inv_spec; fix. Invariant `0 ≤ acc` inferred.
#spec sumPos (xs : List Int) => (r : Int | 0 ≤ r)

def sumAll (xs : List Int) : Int := xs.foldl (· + ·) 0

-- Refined binder: `∀ a ∈ xs, 0 ≤ a` flows into the step clause's oracle.
#spec sumAll (xs : List Int | ∀ a ∈ xs, 0 ≤ a) => (r : Int | 0 ≤ r)

#print axioms sumPos.spec
#print axioms sumAll.spec
