import Flex

/-!
  # Ladder census — the go/no-go measurement (Sep 2026)

  20 `#spec`s over Std `List` combinators (map, filter, foldl, zipWith, take,
  drop, replicate, reverse, append) and user-defined recursion/HOFs, measured
  against three automation tiers. Every number below is *pinned by this file*:
  passes run the tier's tactic; failures are pinned with `fail_if_success`
  and then closed by the next tier (or by hand).

  | tier                                        | closes |
  |---------------------------------------------|--------|
  | rungs 1–2 (unfold/fun_induction + closers — | 12/20  |
  |   "grind with spec patterns", no κ)         |        |
  | + rung 3 / `fix` (foldl κ from qualif bank) | 16/20  |
  | residual (by hand here)                     |  4/20  |

  Reading:
  * The κ-needing fraction is 8/20 (40%) — the paper's territory. The
    grind-with-patterns baseline alone is 60%, so the contribution is
    measurable, not decorative.
  * All four rung-3 recoveries are foldl-accumulator invariants — exactly the
    class `fix` + one qualifier handles, with no invariant written.
  * The residual four are the work items: zipWith elementwise consequences
    and zipWith∘foldl composition (polymorphic combinator specs with
    predicate parameters), recursive composition (`generate`), and nonlinear
    recursion (κ-strengthening). Their hand proofs below are the witnesses
    those items must synthesize.

  Census-driven harness fixes (kept because they moved the number):
  * rung 1 unfolds `at *` — `∀ b ∈ f xs, …` intros its membership into a
    hypothesis, leaving no `f` in the goal (was 5 spurious failures);
  * result refinements may use dot-notation on the result variable
    (`r.length`), substituted as a projection chain;
  * `grind_pattern` registration is best-effort — a top-level `∀ b ∈ r, …`
    refinement has a binder the pattern cannot cover.
-/

-- Tier-1/2-only ladder (no foldl lemma, no fix), for pinning.
syntax "rungs12" ident : tactic
macro_rules
  | `(tactic| rungs12 $f:ident) =>
    `(tactic| first
        | (intros; unfold $f:ident at *; leafClosers; done)
        | (intros; fun_induction $f:ident <;> leafClosers; done))

-- Qualifier bank for the rung-3 recoveries.
@[qualif] def qc_ge_zero (v : Int) : Prop := 0 ≤ v

-- ───────────────────────────────────────────────────────────────────────────
-- Tier 1: rungs 1–2 close these 12
-- ───────────────────────────────────────────────────────────────────────────

def doubleAll (xs : List Int) : List Int := xs.map (· * 2)
#spec doubleAll (xs : List Int) => (r : List Int | r.length = xs.length)
  by rungs12 doubleAll

def incAll (xs : List Int) : List Int := xs.map (· + 1)
#spec incAll (xs : List Int | ∀ a ∈ xs, 0 ≤ a) => (r : List Int | ∀ b ∈ r, 0 < b)
  by rungs12 incAll

def clampAll (lo hi : Int) (xs : List Int) : List Int :=
  xs.map (fun a => max lo (min a hi))
#spec clampAll (lo : Int) (hi : Int | lo ≤ hi) (xs : List Int)
    => (r : List Int | ∀ b ∈ r, lo ≤ b ∧ b ≤ hi)
  by rungs12 clampAll

def keepPos (xs : List Int) : List Int := xs.filter (0 < ·)
#spec keepPos (xs : List Int)
    => (r : List Int | r.length ≤ xs.length ∧ ∀ b ∈ r, 0 < b)
  by rungs12 keepPos

-- Composition through membership: keepPos stays folded, its spec fires.
def keepPos2 (xs ys : List Int) : List Int := keepPos xs ++ keepPos ys
#spec keepPos2 (xs : List Int) (ys : List Int) => (r : List Int | ∀ b ∈ r, 0 < b)
  by rungs12 keepPos2

def zipAdd (xs ys : List Int) : List Int := List.zipWith (· + ·) xs ys
#spec zipAdd (xs : List Int) (ys : List Int)
    => (r : List Int | r.length = min xs.length ys.length)
  by rungs12 zipAdd

def takeN (n : Nat) (xs : List Int) : List Int := xs.take n
#spec takeN (n : Nat) (xs : List Int) => (r : List Int | r.length ≤ xs.length)
  by rungs12 takeN

def dropN (n : Nat) (xs : List Int) : List Int := xs.drop n
#spec dropN (n : Nat) (xs : List Int) => (r : List Int | r.length ≤ xs.length)
  by rungs12 dropN

def pad (n : Nat) : List Int := List.replicate n 0
#spec pad (n : Nat) => (r : List Int | r.length = n ∧ ∀ b ∈ r, b = 0)
  by rungs12 pad

def revCat (xs ys : List Int) : List Int := xs.reverse ++ ys
#spec revCat (xs : List Int) (ys : List Int)
    => (r : List Int | r.length = xs.length + ys.length)
  by rungs12 revCat

def len2 (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | _ :: t => 1 + len2 t
#spec len2 (xs : List Int) => (r : Int | 0 ≤ r)
  by rungs12 len2

-- HOF recursion with an arrow-refined closure binder.
def countIf (p : Int → Bool) (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => if p h then 1 + countIf p t else countIf p t
#spec countIf (p : (i : Int) => (b : Bool | b = true → 0 < i)) (xs : List Int)
    => (r : Int | 0 ≤ r)
  by rungs12 countIf

-- ───────────────────────────────────────────────────────────────────────────
-- Tier 2: rungs 1–2 fail (pinned); rung 3 + fix infer the foldl invariant
-- ───────────────────────────────────────────────────────────────────────────

def total (xs : List Int) : Int := xs.foldl (· + ·) 0
#spec total (xs : List Int | ∀ a ∈ xs, 0 ≤ a) => (r : Int | 0 ≤ r) by
  fail_if_success rungs12 total
  flex_spec_solve total

def sumPos' (xs : List Int) : Int :=
  xs.foldl (fun acc a => if 0 < a then acc + a else acc) 0
#spec sumPos' (xs : List Int) => (r : Int | 0 ≤ r) by
  fail_if_success rungs12 sumPos'
  flex_spec_solve sumPos'

def maxOf (xs : List Int) : Int := xs.foldl max 0
#spec maxOf (xs : List Int) => (r : Int | 0 ≤ r) by
  fail_if_success rungs12 maxOf
  flex_spec_solve maxOf

def countLen (xs : List Int) : Int := xs.foldl (fun acc _ => acc + 1) 0
#spec countLen (xs : List Int) => (r : Int | 0 ≤ r) by
  fail_if_success rungs12 countLen
  flex_spec_solve countLen

-- ───────────────────────────────────────────────────────────────────────────
-- Residual: the full ladder fails (pinned); hand proofs = the witnesses the
-- next work items must synthesize
-- ───────────────────────────────────────────────────────────────────────────

-- zipWith elementwise: needs List.zipWith's polymorphic spec with predicate
-- parameters. The hand proof is the double induction that spec would package.
def zipAdd' (xs ys : List Int) : List Int := List.zipWith (· + ·) xs ys
#spec zipAdd' (xs : List Int | ∀ a ∈ xs, 0 ≤ a) (ys : List Int | ∀ a ∈ ys, 0 ≤ a)
    => (r : List Int | ∀ b ∈ r, 0 ≤ b) by
  fail_if_success flex_spec_solve zipAdd'
  -- NB: the #spec statement interleaves hypotheses with binders:
  -- ∀ xs, hxs → ∀ ys, hys → …
  intro xs hxs
  unfold zipAdd'
  induction xs with
  | nil => simp
  | cons a t ih =>
    -- `induction` auto-reverts and re-introduces hxs (it mentions xs)
    intro ys hy c hc
    cases ys with
    | nil => simp at hc
    | cons b u =>
      rw [List.zipWith_cons_cons] at hc
      rcases List.mem_cons.mp hc with h | h
      · have h1 := hxs a (by simp); have h2 := hy b (by simp); omega
      · exact ih (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) u
          (fun z hz => hy z (List.mem_cons_of_mem _ hz)) c h

-- zipWith ∘ foldl (the Fig. 1 dot): elementwise helper + explicit foldl
-- invariant witness. With zipWith's polymorphic spec registered, this
-- becomes rung 3 alone.
theorem zipMul_nonneg : ∀ xs ys : List Int, (∀ a ∈ xs, 0 ≤ a) →
    (∀ a ∈ ys, 0 ≤ a) → ∀ b ∈ List.zipWith (· * ·) xs ys, 0 ≤ b := by
  intro xs ys
  induction xs generalizing ys with
  | nil => simp
  | cons a t ih => cases ys with
    | nil => simp
    | cons b u =>
      intro hx hy c hc
      rw [List.zipWith_cons_cons] at hc
      rcases List.mem_cons.mp hc with h | h
      · have h1 := hx a (by simp); have h2 := hy b (by simp)
        exact h ▸ Int.mul_nonneg h1 h2
      · exact ih u (fun z hz => hx z (List.mem_cons_of_mem _ hz))
          (fun z hz => hy z (List.mem_cons_of_mem _ hz)) c h

def dot (xs ys : List Int) : Int := (List.zipWith (· * ·) xs ys).foldl (· + ·) 0
#spec dot (xs : List Int | ∀ a ∈ xs, 0 ≤ a) (ys : List Int | ∀ a ∈ ys, 0 ≤ a)
    => (r : Int | 0 ≤ r) by
  fail_if_success flex_spec_solve dot
  intro xs hxs ys hys
  unfold dot
  apply foldl_inv_spec
  exact ⟨(0 ≤ ·),
    fun v hv => by omega,
    fun b hb a ha v hv => by
      have := zipMul_nonneg xs ys hxs hys a ha; omega,
    fun b hb => hb⟩

-- Recursive composition: the leaves need len2's unfolding — generate's
-- PLE-style territory.
def countPos (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => if 0 < h then 1 + countPos t else countPos t
#spec countPos (xs : List Int) => (r : Int | 0 ≤ r ∧ r ≤ len2 xs) by
  fail_if_success flex_spec_solve countPos
  intro xs
  fun_induction countPos <;> (simp only [len2] at *; omega)

-- Nonlinear recursion: 0 < n * fact (n - 1) is beyond the closers; the
-- product-positivity step is one κ-strengthening (or one lemma hint) away.
def fact (n : Int) : Int :=
  if n ≤ 1 then 1 else n * fact (n - 1)
  termination_by n.toNat
  decreasing_by omega
#spec fact (n : Int) => (r : Int | 0 < r) by
  fail_if_success flex_spec_solve fact
  intro n
  fun_induction fact with
  | case1 => omega
  | case2 n h ih => exact Int.mul_pos (by omega) ih

#print axioms total.spec
#print axioms dot.spec
#print axioms countIf.spec
