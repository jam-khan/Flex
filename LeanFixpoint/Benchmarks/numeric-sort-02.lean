/-
  # LiquidHaskell Test: numeric-sort-01 (two-param κ)

  Same sum function but κ1 has two params: `(v, z)` where
  `z` is always instantiated with `zero = 0`.

  Qualifier: `v ≥ z` (relational)
```
  sum n = if n ≤ 0 then 0 else n + sum (n - 1)
```

  κ1(v, zero) means "v is the output, zero is 0"
  The use site checks: κ1(r, 0) ⇒ 0 ≤ r

  Source: `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/numeric-sort-01.smt2`
-/
import LeanFixpoint.Tactic.Command

def k1_ns01 : KVar := { name := `κ1, params := [`v, `z] }

def lhNumericSort01 : Constraint :=
  c{  -- zero = 0 is bound at the top
      ∀ zero : int . zero == 0 ⇒
        -- Base: n ≤ zero ⇒ VV = zero ⇒ κ1(VV, zero)
        [∀ n : int . n ≤ zero ⇒
          ∀ VV : int . VV == zero ⇒ k1_ns01(VV, zero)]
        -- Rec: ¬(n ≤ zero) ⇒ n1 = n-1 ⇒ κ1(t1, zero) ⇒ v = n+t1 ⇒ κ1(v, zero)
      ∧ [∀ n : int . 0 < n ⇒
          ∀ n1 : int . n1 == n - 1 ⇒
            ∀ t1 : int . k1_ns01(t1, zero) ⇒
              ∀ v : int . v == n + t1 ⇒ k1_ns01(v, zero)]
        -- Use: κ1(r, zero) ⇒ zero ≤ r
      ∧ [∀ y : int . true ⇒
          ∀ r : int . k1_ns01(r, zero) ⇒ zero ≤ r] }

#solve_constraint_full lhNumericSort01 with [{ pred := r{ v ≥ 0 } }]
