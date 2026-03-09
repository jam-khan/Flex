import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Macros

/-!
  # Example: Cyclic κ-variable (should fail elimination)
-/

def kappa_sum : KVar := { name := `κsum, params := [`z] }

def sumConstraint : Constraint :=
  c{  -- base case: x = 0 ∧ ν = 0 ⇒ κ(ν)
      -- encode the two hypotheses as nested ∀ binders
      [∀ x : int . 0 ≤ x ⇒
        ∀ ν : int . x == 0 ⇒
          ∀ ν2 : int . ν2 == 0 ⇒ kappa_sum(ν2)]
      -- recursive case: κ(r) in body AND κ(ν) in head
    ∧ [∀ x : int . 0 ≤ x ⇒
        ∀ r : int . kappa_sum(r) ⇒
          ∀ ν : int . ν == x + r ⇒ kappa_sum(ν)]
      -- output: κ(y) ⇒ 0 ≤ y
    ∧ [∀ y : int . kappa_sum(y) ⇒ 0 ≤ y] }

#eval do
  let sc := sumConstraint.scope kappa_sum
  let c' := stripScope kappa_sum sc
  let sol := c'.sol1 kappa_sum
  IO.println s!"sol contains κsum? {sol.kvars.any (· == kappa_sum)}"

-- #solve_constraint sumConstraint
