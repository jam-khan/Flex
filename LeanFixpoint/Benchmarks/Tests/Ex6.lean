import LeanFixpoint.Tactic.Command


/-!
  # Example: Factorial — acyclic setup + cyclic recursion + output property

  Program (conceptual):
```
  fact :: Nat → Nat
  fact x =
    let y = inc x          -- y = x + 1, ensures y ≥ 1
    in factRec y           -- factRec is recursive
```

  where factRec is:
```
  factRec k = if k ≤ 1 then 1 else k * factRec (k - 1)
```

  We want to verify: output is always ≥ 1 (positive).

  - κy is acyclic: y = x + 1 where x ≥ 0, so y ≥ 1
  - κfact is cyclic: recursive, self-dependent
  - κarg is cyclic: input to factRec, constrained by recursive call
-/

def ky2    : KVar := { name := `κy,    params := [`z] }
def karg   : KVar := { name := `κarg,  params := [`z] }
def kfact  : KVar := { name := `κfact, params := [`z] }

def exFact : Constraint :=
  c{  [∀ x : int . 0 ≤ x ⇒
        ∀ ν : int . ν == x + 1 ⇒ ky2(ν)]
    ∧ [∀ y : int . ky2(y) ⇒ karg(y)]
    ∧ [∀ k : int . karg(k) ⇒
        ∀ ν : int . k ≤ 1 ∧ ν == 1 ⇒ kfact(ν)]
    ∧ [∀ k : int . karg(k) ⇒
        ∀ ν : int . 1 < k ∧ ν == k - 1 ⇒ karg(ν)]
    ∧ [∀ k : int . karg(k) ⇒
        ∀ r : int . kfact(r) ⇒
          ∀ ν : int . 1 < k ∧ ν == k ⇒ kfact(ν)]
    ∧ [∀ y : int . kfact(y) ⇒ 1 ≤ y] }

-- Qualifiers needed: 1 ≤ v (positive) for κfact, 1 ≤ v for κarg
#solve_constraint_full exFact with [{ pred := r{ 1 ≤ v } }, { pred := r{ 0 ≤ v } }]
