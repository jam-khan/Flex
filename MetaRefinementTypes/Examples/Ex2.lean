import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Macros

/-
  **Example 2**
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
-/

/-
  Step 1: Generate Templates

    x     :: {v : Int | v ≥ 0}
    n     :: {v : Int | v = x - 1}
    p     :: {v : Int | v = x + 1}
    xs    :: List {v : Int | κx(v)}
    ys    :: List {v : Int | κy(v)}
    y     :: {v : Int | κy(v)}
    inc y :: {v : Int | v = y + 1}

    κx and κy are fresh refinement variables

  Step 2: Generate Constraints

    ∀x:int. 0 ≤ x ⇒
      ∀n:int. n = x - 1 ⇒
        ∀p:int. p = x + 1 ⇒
            ∀ν. ν = n ⇒ κx(ν)                    (4)
          ∧ ∀ν. ν = p ⇒ κy(ν)                    (5)
          ∧ ∀ν. κx(ν) ⇒ κy(ν)                    (6)
          ∧ ∀y. κy(y) ⇒ ∀ν. ν = y + 1 ⇒ 0 ≤ ν   (7)

    (4): n is cons-ed into xs, so {v | v = n} <: {v | κx(v)}
    (5): p is cons-ed into ys, so {v | v = p} <: {v | κy(v)}
    (6): xs flows into ys,     so {v | κx(v)} <: {v | κy(v)}
    (7): output of inc y must be Nat

  Step 3: Solution

    Eliminate κx first (it only flows into κy), then κy.

    κx(z) ≡ ∃x. 0 ≤ x ∧ ∃n. n = x - 1 ∧ ∃p. p = x + 1 ∧ ∃ν. ν = n ∧ z = ν
           simplified: 0 ≤ z + 1

    κy(z) ≡ (∃ν. ν = p ∧ z = ν)           -- from (5)
           ∨ (∃ν. κx(ν) ∧ z = ν)           -- from (6), κx substituted
           simplified: 0 ≤ z + 1

    Substituting κy into (7) yields a valid formula.
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

def ex2Eliminated := ex2Constraint.elim [kappa_x, kappa_y]

#eval ex2Constraint.kvars
#eval ex2Eliminated.kvars

#check_vc ex2Eliminated

/-
  κx justified by constraint (4):
  given 0 ≤ x, n = x - 1, p = x + 1, ν = n,
  we can witness κx(ν)
-/
theorem ex2_kappa_x_solution :
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          ∀ ν : Int, ν = n →
            ∃ ν', ν' = n ∧ ν = ν' := by
  grind

/-
  κy justified by constraints (5) and (6):
  y satisfies κy if it came from p directly,
  or from something satisfying κx
-/
theorem ex2_kappa_y_solution :
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          ∀ y : Int,
            ((∃ ν', ν' = p ∧ y = ν')
            ∨ (∃ ν', (∃ ν'', ν'' = n ∧ ν' = ν'') ∧ y = ν')) →
            ∃ ν', (ν' = p ∨ ∃ ν'', ν'' = n ∧ ν' = ν'') ∧ y = ν' := by
  grind

/-
  Final VC: κy's solution is strong enough to
  guarantee the output type 0 ≤ ν
-/
theorem ex2_kappa_soundness :
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          ∀ y : Int,
            ((∃ ν', ν' = p ∧ y = ν')
            ∨ (∃ ν', (∃ ν'', ν'' = n ∧ ν' = ν'') ∧ y = ν')) →
            ∀ ν : Int, ν = y + 1 → 0 ≤ ν := by
  grind
