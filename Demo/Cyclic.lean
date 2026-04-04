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

-- PA1: 1 fusion κ + 1 PA κ
def pa1 : Prop :=
  ∃ κseed : Int → Prop,
  ∃ κinv  : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 2 → κseed ν)
    ∧ (∀ v : Int, κseed v → κinv v)
    ∧ (∀ i : Int, κinv i ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν)   -- loop body, κinv in body AND head → cyclic
    ∧ (∀ i : Int, κinv i → 0 ≤ i)

theorem pa1_proof : pa1 := by
  try solve_fixpoint with Q_pa
  sorry

-- PA2: 2 fusion κ merging into 1 PA κ
-- The weaker source (κlo from x, gives 0 ≤ ν) dominates; GE2/GTZ eliminated.
def pa2 : Prop :=
  ∃ κlo  : Int → Prop,
  ∃ κhi  : Int → Prop,
  ∃ κinv : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x     → κlo ν)
    ∧ (∀ ν : Int, ν = x + 4 → κhi ν)
    ∧ (∀ v : Int, κlo v → κinv v)
    ∧ (∀ v : Int, κhi v → κinv v)
    ∧ (∀ i : Int, κinv i ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν)
    ∧ (∀ i : Int, κinv i → 0 ≤ i)

theorem pa2_proof : pa2 := by
  try solve_fixpoint with Q_pa
  sorry

-- PA3: fusion pre-compute, PA loop (step-2), independent fusion output
-- κout from x+3: 3 ≤ r post-check only closes via fusion's exact bound, not PA.
def pa3 : Prop :=
  ∃ κpre : Int → Prop,
  ∃ κinv : Int → Prop,
  ∃ κout : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κpre ν)
    ∧ (∀ ν : Int, ν = x + 3 → κout ν)
    ∧ (∀ v : Int, κpre v → κinv v)
    ∧ (∀ i : Int, κinv i ∧ 2 ≤ i →
        ∀ ν : Int, ν = i - 2 → κinv ν)   -- step-2 loop; cyclic
    ∧ (∀ i : Int, κinv i → 0 ≤ i)
    ∧ (∀ r : Int, κout r → 3 ≤ r)

theorem pa3_proof : pa3 := by
  try solve_fixpoint with Q_pa
  sorry

-- PA4: 1 fusion κ, two independent PA loops
-- κlp1 seeded from x directly; κlp2 seeded via the fusion κfused.
def pa4 : Prop :=
  ∃ κfused : Int → Prop,
  ∃ κlp1   : Int → Prop,
  ∃ κlp2   : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κfused ν)
    ∧ (∀ ν : Int, ν = x     → κlp1 ν)
    ∧ (∀ i : Int, κlp1 i ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κlp1 ν)
    ∧ (∀ i : Int, κlp1 i ∧ 0 ≤ i)
    ∧ (∀ v : Int, κfused v → κlp2 v)
    ∧ (∀ i : Int, κlp2 i ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κlp2 ν)
    ∧ (∀ i : Int, κlp2 i → 0 ≤ i)
    ∧ (∀ r : Int, κfused r → 1 ≤ r)

theorem pa4_proof : pa4 := by
  try solve_fixpoint with Q_pa
  sorry

-- PA5: two-step fusion chain → PA loop + independent fusion
-- κa (x+1) → κb (κa+1): acyclic 2-step chain, both handled by fusion.
-- κinv: PA loop seeded from κb; 5 ≤ r post-check on κfin requires fusion, not PA.
def pa5 : Prop :=
  ∃ κa   : Int → Prop,
  ∃ κb   : Int → Prop,
  ∃ κinv : Int → Prop,
  ∃ κfin : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κa ν)
    ∧ (∀ v : Int, κa v → ∀ ν : Int, ν = v + 1 → κb ν)
    ∧ (∀ v : Int, κb v → κinv v)
    ∧ (∀ i : Int, κinv i ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν)
    ∧ (∀ i : Int, κinv i → 0 ≤ i)
    ∧ (∀ ν : Int, ν = x + 5 → κfin ν)
    ∧ (∀ r : Int, κfin r → 5 ≤ r)

theorem pa5_proof : pa5 := by
  try solve_fixpoint with Q_pa
  sorry
