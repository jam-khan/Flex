/-
  LiquidHaskell Test: sum with type alias (Apple = Int)
```
  sum n = if n ≤ 0 then 0 else n + sum (n - 1)
```
  Qualifier: v ≥ 0
  κ1 is cyclic (recursive)

  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/numeric-sort-00.smt2`
-/
import LeanFixpoint.Tactic.Command

def kApple : KVar := { name := `κ1, params := [`v] }

def lhAppleSum : Constraint :=
  c{  -- Base: n ≤ 0 ⇒ VV = 0 ⇒ κ1(VV)
      [∀ n : int . n ≤ 0 ⇒
        ∀ VV : int . VV == 0 ⇒ kApple(VV)]
      -- Rec: ¬(n ≤ 0) ⇒ n1 = n-1 ⇒ κ1(t1) ⇒ v = n+t1 ⇒ κ1(v)
    ∧ [∀ n : int . 0 < n ⇒
        ∀ n1 : int . n1 == n - 1 ⇒
          ∀ t1 : int . kApple(t1) ⇒
            ∀ v : int . v == n + t1 ⇒ kApple(v)]
      -- Use: κ1(r) ⇒ 0 ≤ r
    ∧ [∀ y : int . true ⇒
        ∀ r : int . kApple(r) ⇒ 0 ≤ r] }

#solve_constraint_full lhAppleSum with [{ pred := r{ 0 ≤ v } }]
