import LeanFixpoint

/-
  Predicate Abstraction Demo

  Five examples with a mix of acylic and cyclic kvars
-/

def Q_pa : List Qualifier := [
  q{ GEZ(v : int)  | 0 ≤ v  },
  q{ GTZ(v : int)  | 0 ≤ v  },
  q{ GE2(v : int)  | 2 ≤ v  },
  q{ GEm1(v : int) | -1 ≤ v },
  q{ LEZ(v : int)  | v ≤ 0  },
  q{ LE1(v : int)  | v ≤ 1  }
]

-- CYC0: simplest cyclic — single κ with self-loop, no acyclic κ-vars
-- κ seeded from x (where 0 ≤ x), loop decrements by 1, check 0 ≤ result
-- Expected solution: κ ↦ 0 ≤ z
def cyc0 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κ ν x)                                      -- seed
    ∧ (∀ i : Int, κ i x ∧ 1 ≤ i → ∀ ν : Int, ν = i - 1 → κ ν x)  -- loop (cyclic)
    ∧ (∀ i : Int, κ i x → 0 ≤ i)                                      -- check

theorem cyc0_proof : cyc0 := by
  -- unfold cyc0
  -- exists (fun z => 0 ≤ z)
  -- grind
  solve_fixpoint with Q_pa



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
  solve_fixpoint with Q_pa

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
  solve_fixpoint with Q_pa


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
  solve_fixpoint with Q_pa


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
  solve_fixpoint with Q_pa

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
  solve_fixpoint with Q_pa

def Q_pa2 : List Qualifier := Q_pa ++ [
  q{ Le(a : int, b : int) | a ≤ b }
]

-- PA6: Multi-parameter κ-vars (2 acyclic + 2 cyclic)
-- Counter from 0 to n, accumulator tracks sum.
-- κseed, κhi are acyclic; κcnt(i,n), κacc(a,n) are cyclic with 2 params.
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

theorem pa6_proof : pa6 := by
  solve_fixpoint with Q_pa2

