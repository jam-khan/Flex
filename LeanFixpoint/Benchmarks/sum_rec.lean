/-
  Liquid Haskell example
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/sum-rec.smt2`
-/
import LeanFixpoint.Tactic.Command

def k1 : KVar := { name := `κ1, params := [`v, `n] }

def lhSum : Constraint :=
  c{  -- Base case: n ≤ 0 ⇒ VV = 0 ⇒ κ1(VV, n)
      [∀ n : int . true ⇒
        ∀ VV : int . n ≤ 0 ∧ VV == 0 ⇒ k1(VV, n)]
      -- Recursive case: ¬(n ≤ 0) ⇒ n1 = n-1 ⇒ κ1(t1, n1) ⇒ v = n+t1 ⇒ κ1(v, n1)
    ∧ [∀ n : int . true ⇒
        ∀ n1 : int . 0 < n ∧ n1 == n - 1 ⇒
          ∀ t1 : int . k1(t1, n1) ⇒
            ∀ vv : int . vv == n + t1 ⇒ k1(vv, n1)]
      -- Use: κ1(r, y) ⇒ 0 ≤ r
    ∧ [∀ y : int . true ⇒
        ∀ r : int . k1(r, y) ⇒ 0 ≤ r] }

-- #solve_constraint_full lhSum with [{ pred := r{ 0 < v } }]
