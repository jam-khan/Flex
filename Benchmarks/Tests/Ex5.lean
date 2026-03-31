import LeanFixpoint



/-!
  # Example: Mixed Acyclic + Cyclic Constraints

  Program (conceptual):
```
  ex_mixed :: Nat → Nat
  ex_mixed x =
    let y = dec x          -- y = x - 1, type needs κy
    in sum y               -- sum is recursive, type needs κsum
```

  - κy is acyclic: assigned from `dec x`, used as input to `sum`
  - κsum is cyclic: recursive function, self-dependent

  ## Constraints

  Acyclic (κy):
    (1) ∀x. 0≤x ⇒ ∀ν. ν = x-1 ⇒ κy(ν)       — dec x flows into κy
    (2) ∀y. κy(y) ⇒ κsum(y)                     — y passed to sum

  Cyclic (κsum):
    (3) ∀k. 0≤k ⇒ ∀ν. k==0 ∧ ν==0 ⇒ κsum(ν)   — base case
    (4) ∀k. 0≤k ⇒ ∀r. κsum(r) ⇒
          ∀ν. ν==k+r ⇒ κsum(ν)                   — recursive case
    (5) ∀y. κsum(y) ⇒ 0≤y                        — output must be Nat

  ## Expected behavior

  Phase 1 (Fusion): eliminate κy exactly
    κy(z) = ∃x. 0≤x ∧ ∃ν. ν=x-1 ∧ z=ν  (simplifies to 0≤z+1)

  Phase 2 (Predicate abstraction): solve κsum with Q = {0≤v}
    Init:  A(κsum) = {0≤z}
    Base:  0≤k ∧ k==0 ∧ ν==0 ⇒ 0≤ν  ✓
    Rec:   0≤k ∧ 0≤r ∧ ν==k+r ⇒ 0≤ν   ✓
    Final: A(κsum) = {0≤z}

  Phase 3: substitute and check residual VC ✅
-/

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
