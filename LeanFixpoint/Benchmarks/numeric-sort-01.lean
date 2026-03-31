/-
  # LiquidHaskell Test: numeric-sort-01

  Same sum function but with `numeric Apple` type alias.
  `Apple` is just `Int` — `numeric` in liquid-fixpoint means
  the sort supports arithmetic.
```
  sum n = if n ≤ 0 then 0 else n + sum (n - 1)
```

  The original encoding uses explicit boolean guard variables
  (`cond`, `grd`, `ok1`) to model `if-then-else` with path
  sensitivity. We preserve this structure faithfully.

  Qualifier: `v ≥ 0`
  κ1 is cyclic (recursive)

  Source: `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/numeric-sort-01.smt2`
-/
import LeanFixpoint.Tactic.Command

def k1_ns01 : KVar := { name := `κ1, params := [`v] }

def lhNumericSort01 : Constraint :=
  c{  -- Branch encoding: ∀n. ∀cond. cond ⟺ (n ≤ 0)
      -- Then branch: cond ⇒ VV = 0 ⇒ κ1(VV)
      [∀ n : int . true ⇒
        ∀ VV : int . n ≤ 0 ∧ VV == 0 ⇒ k1_ns01(VV)]
      -- Else branch: ¬cond ⇒ n1 = n-1 ⇒ κ1(t1) ⇒ v = n+t1 ⇒ κ1(v)
    ∧ [∀ n : int . true ⇒
        ∀ n1 : int . 0 < n ∧ n1 == n - 1 ⇒
          ∀ t1 : int . k1_ns01(t1) ⇒
            ∀ v : int . v == n + t1 ⇒ k1_ns01(v)]
      -- Use: κ1(r) ⇒ 0 ≤ r (asserted via boolean encoding)
    ∧ [∀ y : int . true ⇒
        ∀ r : int . k1_ns01(r) ⇒ 0 ≤ r] }

-- #solve_constraint_full lhNumericSort01 with [{ pred := r{ 0 ≤ v } }]
