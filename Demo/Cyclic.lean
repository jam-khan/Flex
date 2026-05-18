import LeanFixpoint

/-
  Predicate Abstraction Demo — updated for `@[qualif]`-lambda syntax.

  Mix of acyclic and cyclic κ-var examples. Each theorem uses
  `solve_fusion`, which after Step 6 wiring will automatically run fusion
  for acyclic κ's and predicate-abstraction for cyclic κ's, drawing
  qualifiers from any in-scope `@[qualif]` declaration.

  NOTE: Until Step 6 is merged, `solve_fusion` only handles acyclic κ's.
  Every test below has at least one cyclic κ, so they currently fail.
  They are written in their final form so a single edit to `SolveFusion.lean`
  makes them all attempt a proof; the qualifier set is believed to be
  sufficient but awaits end-to-end verification.
-/

@[qualif] def q_gez  (v : Int)   : Prop := 0 ≤ v
@[qualif] def q_gtz  (v : Int)   : Prop := 0 < v
@[qualif] def q_ge2  (v : Int)   : Prop := 2 ≤ v
@[qualif] def q_gem1 (v : Int)   : Prop := -1 ≤ v
@[qualif] def q_lez  (v : Int)   : Prop := v ≤ 0
@[qualif] def q_le1  (v : Int)   : Prop := v ≤ 1
@[qualif] def q_le   (a b : Int) : Prop := a ≤ b

-- CYC0: simplest cyclic — single κ with self-loop, no acyclic κ-vars
-- κ seeded from x (where 0 ≤ x), loop decrements by 1, check 0 ≤ result
-- Expected solution: κ[ν, x] ↦ 0 ≤ ν   (contributed by `q_gez` at slot [0])
def cyc0 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κ ν x)                                  -- seed
    ∧ (∀ i : Int, κ i x ∧ 1 ≤ i → ∀ ν : Int, ν = i - 1 → κ ν x)  -- loop (cyclic)
    ∧ (∀ i : Int, κ i x → 0 ≤ i)                                  -- check

theorem cyc0_proof : cyc0 := by
  try solve_fixpoint

-- PA1: 1 fusion κ + 1 PA κ
def pa1 : Prop :=
  ∃ κseed : Int → Int → Prop,
  ∃ κinv  : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 2 → κseed ν x)
    ∧ (∀ v : Int, κseed v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)

theorem pa1_proof : pa1 := by
  try solve_fixpoint

-- PA2: 2 fusion κ merging into 1 PA κ
-- The weaker source (κlo from x, gives 0 ≤ ν) dominates; GE2/GTZ eliminated.
def pa2 : Prop :=
  ∃ κlo  : Int → Int → Prop,
  ∃ κhi  : Int → Int → Prop,
  ∃ κinv : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x     → κlo ν x)
    ∧ (∀ ν : Int, ν = x + 4 → κhi ν x)
    ∧ (∀ v : Int, κlo v x → κinv v x)
    ∧ (∀ v : Int, κhi v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)

theorem pa2_proof : pa2 := by
  try solve_fixpoint

-- PA3: fusion pre-compute, PA loop (step-2), independent fusion output
-- κout from x+3: 3 ≤ r post-check only closes via fusion's exact bound, not PA.
def pa3 : Prop :=
  ∃ κpre : Int → Int → Prop,
  ∃ κout : Int → Int → Prop,
  ∃ κinv : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κpre ν x)
    ∧ (∀ ν : Int, ν = x + 3 → κout ν x)
    ∧ (∀ v : Int, κpre v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 2 ≤ i →
        ∀ ν : Int, ν = i - 2 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)
    ∧ (∀ r : Int, κout r x → 3 ≤ r)

theorem pa3_proof : pa3 := by
  try solve_fixpoint

-- PA4: 1 fusion κ, two independent PA loops
-- κlp1 seeded from x directly; κlp2 seeded via the fusion κfused.
def pa4 : Prop :=
  ∃ κfused : Int → Int → Prop,
  ∃ κlp1   : Int → Int → Prop,
  ∃ κlp2   : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κfused ν x)
    ∧ (∀ ν : Int, ν = x     → κlp1 ν x)
    ∧ (∀ i : Int, κlp1 i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κlp1 ν x)
    ∧ (∀ i : Int, κlp1 i x → 0 ≤ i)
    ∧ (∀ v : Int, κfused v x → κlp2 v x)
    ∧ (∀ i : Int, κlp2 i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κlp2 ν x)
    ∧ (∀ i : Int, κlp2 i x → 0 ≤ i)
    ∧ (∀ r : Int, κfused r x → 1 ≤ r)

theorem pa4_proof : pa4 := by
  try solve_fixpoint

-- PA5: two-step fusion chain → PA loop + independent fusion
-- κa (x+1) → κb (κa+1): acyclic 2-step chain, both handled by fusion.
-- κinv: PA loop seeded from κb; 5 ≤ r post-check on κfin requires fusion, not PA.
def pa5 : Prop :=
  ∃ κa   : Int → Int → Prop,
  ∃ κb   : Int → Int → Prop,
  ∃ κfin : Int → Int → Prop,
  ∃ κinv : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κa ν x)
    ∧ (∀ v : Int, κa v x → ∀ ν : Int, ν = v + 1 → κb ν x)
    ∧ (∀ v : Int, κb v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)
    ∧ (∀ ν : Int, ν = x + 5 → κfin ν x)
    ∧ (∀ r : Int, κfin r x → 5 ≤ r)

theorem pa5_proof : pa5 := by
  try solve_fixpoint

-- PA6: Multi-parameter κ-vars (2 acyclic + 2 cyclic)
-- Counter from 0 to n, accumulator tracks sum.
-- κseed, κhi are acyclic; κcnt(i,n), κacc(a,n) are cyclic with 2 params.
-- Uses `q_le` (2-arg) in addition to the 1-arg qualifier bank.
def pa6 : Prop :=
  ∃ κseed : Int → Int → Prop,
  ∃ κhi   : Int → Int → Prop,
  ∃ κcnt  : Int → Int → Int → Prop,
  ∃ κacc  : Int → Int → Int → Prop,
    ∀ n : Int, 0 ≤ n →
      (∀ ν : Int, ν = 0 → κseed ν n)
    ∧ (∀ ν : Int, ν = n → κhi ν n)
    ∧ (∀ v : Int, κseed v n → ∀ b : Int, κhi b n → κcnt v b n)
    ∧ (∀ v : Int, κseed v n → ∀ b : Int, κhi b n → κacc v b n)
    ∧ (∀ i m : Int, κcnt i m n → i < m →
        ∀ a : Int, κacc a m n →
          (∀ ν : Int, ν = i + 1 → κcnt ν m n)
        ∧ (∀ ν : Int, ν = a + i → κacc ν m n))
    ∧ (∀ i m : Int, κcnt i m n → i ≥ m →
        ∀ a : Int, κacc a m n → 0 ≤ a)

set_option maxHeartbeats 1600000 in
theorem pa6_proof : pa6 := by
  try solve_fixpoint

-- PA7: Witness-order regression test.
-- Declares cyclic κ before acyclic κ so existential order differs
-- from solver's current acyclic-then-cyclic solution order.
def pa7 : Prop :=
  ∃ κinv  : Int → Int → Int → Prop,
  ∃ κseed : Int → Int → Prop,
    ∀ n : Int, 0 ≤ n →
      (∀ ν : Int, ν = 0 → κseed ν n)
    ∧ (∀ v : Int, κseed v n → κinv v n n)
    ∧ (∀ i b : Int, κinv i b n → i < b →
        ∀ ν : Int, ν = i + 1 → κinv ν b n)
    ∧ (∀ i b : Int, κinv i b n → i ≥ b → 0 ≤ i)

theorem pa7_proof : pa7 := by
  solve_fixpoint

/-
  fusion
  - reorder: cyclic first, then topo sort acyclic
  - eliminates acylic kvars
  - leaving cyclic as meta-vars to provide
  - prop intact, not flattened, head κ gone

  flatten
  - if any existential, leaves as meta-vars
  - flattens a prop

  fixpoint
  - predicate abstraction
  - assumes kappa as meta-vars
  - existentials handle too
-/
