import Lean

import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Command

/-!
  # Example 2 — Collections (Local Refinement Typing, §2)

  ```
  ex2 :: Nat → Nat
  ex2 x =
    let ys = let n = dec x
                 p = inc x
                 xs = n : []
             in p : xs
        y = last ys
    in inc y
  ```

  Templates:
    x :: {v : Int | v ≥ 0},  n :: {v | v = x-1},  p :: {v | v = x+1}
    xs :: List {v | κx(v)},   ys :: List {v | κy(v)}
    y  :: {v | κy(v)},        inc y :: {v | v = y+1}

  Constraints (4)–(7):
    (4) ∀ν. ν = n   ⇒ κx(ν)      — n cons-ed into xs
    (5) ∀ν. ν = p   ⇒ κy(ν)      — p cons-ed into ys
    (6) ∀ν. κx(ν)   ⇒ κy(ν)      — xs flows into ys
    (7) ∀y. κy(y)   ⇒ ∀ν. ν=y+1 ⇒ 0≤ν  — output must be Nat

  Elimination order: κx then κy (κx only flows into κy).

  Scoped solutions:
    κx(z) = ∃ν. ν = n ∧ z = ν
    κy(z) = (∃ν. ν = p ∧ z = ν) ∨ (∃ν. κx_sol(ν) ∧ z = ν)

  Both simplify to 0 ≤ z + 1, verifying ex2.
-/

def kappa_x : KVar := { name := `κx, params := [`z] }
def kappa_y : KVar := { name := `κy, params := [`z] }

def ex2Constraint : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒
      ∀ n : int . n == x - 1 ⇒
        ∀ p : int . p == x + 1 ⇒
            [∀ ν : int . ν == n ⇒ kappa_x(ν)]
          ∧ [∀ ν : int . ν == p ⇒ kappa_y(ν)]
          ∧ [∀ ν : int . kappa_x(ν) ⇒ kappa_y(ν)]
          ∧ [∀ y : int . kappa_y(y) ⇒
              ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν] }

-- Solve everything automatically
#solve_constraint ex2Constraint
