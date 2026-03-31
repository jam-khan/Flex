import LeanFixpoint


/-!
  # Example: Cyclic κ-variable (should fail elimination)
-/

def kappa_sum : KVar := { name := `κsum, params := [`z] }

def sumConstraint : Constraint :=
  c{  [∀ x : int . 0 ≤ x ⇒
        ∀ ν : int . x == 0 ⇒
          ∀ ν2 : int . ν2 == 0 ⇒ kappa_sum(ν2)]
    ∧ [∀ x : int . 0 ≤ x ⇒
        ∀ r : int . kappa_sum(r) ⇒
          ∀ ν : int . ν == x + r ⇒ kappa_sum(ν)]
    ∧ [∀ y : int . kappa_sum(y) ⇒ 0 ≤ y] }


-- #solve_constraint sumConstraint
