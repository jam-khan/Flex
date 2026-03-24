import LeanFixpoint.Tactic.Command


def kappa : KVar := { name := `κ, params := [`z] }

def ex1Constraint' : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒
      [∀ ν : int . ν == x - 1 ⇒ kappa(ν)]
    ∧ [∀ y : int . kappa(y) ⇒
        ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν] }

#solve_constraint ex1Constraint'

def ex1Constraint : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

theorem ex1Proof : ex1Constraint := by
  unfold ex1Constraint
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ ν : Int, ν = x - 1 ∧ z = ν
  grind

def kappa_x : KVar := { name := `κx, params := [`z] }
def kappa_y : KVar := { name := `κy, params := [`z] }

def ex2Constraint' : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒
      ∀ n : int . n == x - 1 ⇒
        ∀ p : int . p == x + 1 ⇒
            [∀ ν : int . ν == n ⇒ kappa_x(ν)]
          ∧ [∀ ν : int . ν == p ⇒ kappa_y(ν)]
          ∧ [∀ ν : int . kappa_x(ν) ⇒ kappa_y(ν)]
          ∧ [∀ y : int . kappa_y(y) ⇒
              ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν] }

#solve_constraint ex2Constraint'

theorem ex2Eliminated :
  ∀ x : Int, 0 ≤ x →
    ∀ n : Int, n = x - 1 →
      ∀ p : Int, p = x + 1 →
        (∀ ν : Int, ν = n → True)
      ∧ (∀ ν : Int, ν = p → True)
      ∧ (∀ ν : Int, (∃ α : Int, α = n ∧ ν = α) → True)
      ∧ (∀ y : Int,
          ((∃ ν : Int, ν = p ∧ y = ν) ∨ (∃ ν : Int, (∃ α : Int, α = n ∧ ν = α) ∧ y = ν)) →
          ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  grind

def ex2Constraint : Prop :=
  ∃ κx : Int → Prop, ∃ κy : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          (∀ ν : Int, ν = n → κx ν)
        ∧ (∀ ν : Int, ν = p → κy ν)
        ∧ (∀ ν : Int, κx ν → κy ν)
        ∧ (∀ y : Int, κy y →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

theorem ex2Proof : ex2Constraint := by
  unfold ex2Constraint
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ ν : Int, ν = n ∧ z = ν
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ n : Int, n = x - 1 ∧ ∃ p : Int, p = x + 1 ∧
    ((∃ ν : Int, ν = p ∧ z = ν) ∨ (∃ ν : Int, (∃ α : Int, α = n ∧ ν = α) ∧ z = ν))
  intro x hx n hn p hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ν hν
    exact ⟨x, hx, n, hn, ν, hν, rfl⟩
  · intro ν hν
    exact ⟨x, hx, n, hn, p, hp, Or.inl ⟨ν, hν, rfl⟩⟩
  · intro ν ⟨x', hx', n', hn', ν', hν'eq, hzν⟩
    exact ⟨x', hx', n', hn', x' + 1, by omega,
           Or.inr ⟨ν', ⟨n', rfl, hν'eq⟩, hzν⟩⟩
  · intro y ⟨x', hx', n', hn', p', hp', hy⟩ ν hν
    grind


def ex3Constraint : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν)

theorem ex3Proof : ex3Constraint := by
  unfold ex3Constraint
  exists fun z => ∃ ν : Int, 0 ≤ ν ∧ z = ν
  exists fun z => ∃ a : Int, (∃ ν : Int, 0 ≤ ν ∧ a = ν) ∧ ∃ ν : Int, ν = a - 1 ∧ z = ν
  exists fun z => ∃ b : Int, (∃ a : Int, (∃ ν : Int, 0 ≤ ν ∧ a = ν) ∧ ∃ ν : Int, ν = a - 1 ∧ b = ν) ∧ ∃ ν : Int, ν = b + 1 ∧ z = ν
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ⟨ν', hν', ha⟩ ν hν
    exact ⟨a, ⟨ν', hν', ha⟩, ν, hν, rfl⟩
  · intro b ⟨a, ha, ν', hν', hb⟩ ν hν
    exact ⟨b, ⟨a, ha, ν', hν', hb⟩, ν, hν, rfl⟩
  · intro ν hν
    exact ⟨ν, hν, rfl⟩
  · intro ν ⟨b, ⟨a, ⟨ν', hν', ha⟩, ν'', hν'', hb⟩, ν''', hν''', hzν⟩
    omega

def ky   : KVar := { name := `κy,   params := [`z] }
def ksum : KVar := { name := `κsum, params := [`z] }

def exMixed : Constraint :=
  c{  [∀ x : int . 0 ≤ x ⇒
        ∀ ν : int . ν == x - 1 ⇒ ky(ν)]
    ∧ [∀ y : int . ky(y) ⇒ ksum(y)]
    ∧ [∀ k : int . 0 ≤ k ⇒
        ∀ ν : int . k == 0 ∧ ν == 0 ⇒ ksum(ν)]
    ∧ [∀ k : int . 0 ≤ k ⇒
        ∀ r : int . ksum(r) ⇒
          ∀ ν : int . ν == k + r ⇒ ksum(ν)]
    ∧ [∀ y : int . ksum(y) ⇒ 0 ≤ y] }

#solve_constraint_full exMixed with [{ pred := r{ 0 ≤ v } }, { pred := r{ v ≤ 0 } }]

def exMixedConstraint : Prop :=
  ∃ κy : Int → Prop, ∃ κsum : Int → Prop,
    (∀ x : Int, 0 ≤ x → ∀ ν : Int, ν = x - 1 → κy ν)
  ∧ (∀ y : Int, κy y → κsum y)
  ∧ (∀ k : Int, 0 ≤ k → ∀ ν : Int, k = 0 ∧ ν = 0 → κsum ν)
  ∧ (∀ k : Int, 0 ≤ k → ∀ r : Int, κsum r → ∀ ν : Int, ν = k + r → κsum ν)
  ∧ (∀ y : Int, κsum y → 0 ≤ y)

theorem exMixedProof : exMixedConstraint := by
  unfold exMixedConstraint
  exists fun z => ∃ x : Int, 0 ≤ x ∧ ∃ ν : Int, ν = x - 1 ∧ z = ν
  exists fun z => 0 ≤ z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Clause 1: ∀ x, 0 ≤ x → ∀ ν, ν = x - 1 → κy ν
  · intro x hx ν hν
    exact ⟨x, hx, ν, hν, rfl⟩
  -- Clause 2: ∀ y, κy y → κsum y  (i.e., 0 ≤ y)
  · intro y ⟨x, hx, ν, hν, hy⟩
    sorry
  -- Clause 3: ∀ k, 0 ≤ k → ∀ ν, k = 0 ∧ ν = 0 → κsum ν  (i.e., 0 ≤ ν)
  · intro k hk ν ⟨hk0, hν0⟩
    omega
  -- Clause 4: ∀ k, 0 ≤ k → ∀ r, κsum r → ∀ ν, ν = k + r → κsum ν
  · intro k hk r hr ν hν
    omega
  -- Clause 5: ∀ y, κsum y → 0 ≤ y
  · intro y hy
    exact hy
