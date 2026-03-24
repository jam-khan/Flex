/-
  # LiquidHaskell Test: numeric-sort-02 (two numeric sorts, cast)

  Same sum but with two numeric type aliases (Apple, Banana).
  `cast v Int` is identity since both are just Int.
  κ1(v : Apple, z : Banana) — cross-sort κ.

  Source: `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/numeric-sort-02.smt2`
-/
import LeanFixpoint.Tactic.Command

def k1_ns02 : KVar := { name := `κ1, params := [`v, `z] }

def lhNumericSort02 : Constraint :=
  c{ ∀ zero : int . zero == 0 ⇒
        [∀ n : int . n ≤ zero ⇒
          ∀ VV : int . VV == zero ⇒ k1_ns02(VV, zero)]
      ∧ [∀ n : int . 0 < n ⇒
          ∀ n1 : int . n1 == n - 1 ⇒
            ∀ t1 : int . k1_ns02(t1, zero) ⇒
              ∀ v : int . v == n + t1 ⇒ k1_ns02(v, zero)]
      ∧ [∀ y : int . true ⇒
          ∀ r : int . k1_ns02(r, zero) ⇒ zero ≤ r] }

#solve_constraint_full lhNumericSort02 with [{ pred := r{ v ≥ 0 } }]
