import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Macros

/-
  **Example 1**

  ```
  ex1 :: Nat → Nat
  ex1 x =
    let y =
      let t = x
      in
        dec t
    in
      inc y
  ```
-/

/-
  Step 1: Generate Templates

    x     :: {v : Int | v ≥ 0}
    t     :: {v : Int | v = x}
    dec t :: {v : Int | v = t - 1}
    y     :: {v : Int | κ(v)}
    inc y :: {v : Int | v = y + 1}

    κ is a refinement variable that is generated fresh

  Step 2: Generate Constraints

    Below is the generated constraint for ex1:

    ∀x:int. 0 ≤ x ⇒
                    ∀v. v = x - 1 ⇒ κ(v)    (1)
      ∧ ∀y. κ(y)  ⇒ ∀v. v = y + 1 ⇒ 0 ≤ v   (2)

    Note: shared binders are explicit in NNF constraint.
    So, binder `x` in the source program is also
    shared by implication (1) and (2).

  Step 3: Solution

    Based on literature, if we have
    implication of the form: Pᵢ => κ(v)
    then we can assign κ to the disjunction
    κ(x) ≡ ∨ᵢ Pᵢ

  In example 1,
    `κ(z) = ∃x. 0 ≤ x ∨ (∃v. v = x - 1 ∧ v = z)`

  simplifying to
    `κ(z) = 0 ≤ z + 1`

-/


def kappa : KVar := { name := `κ, params := [`z] }

def ex1Constraint : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒
      [∀ ν : int . ν == x - 1 ⇒ kappa(ν)]
    ∧ [∀ y : int . kappa(y) ⇒
        ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν] }

def ex1Eliminated := ex1Constraint.elim1 kappa

-- Below is apparently wrong, it only eliminates one κ variable
#eval ex1Constraint.kvars
#eval ex1Constraint.elim1 kappa
#eval (ex1Constraint.elim1 kappa)
#eval ex1Eliminated.kvars

theorem ex1_kappa_solution :
    ∀ x : Int, 0 ≤ x →
      ∀ ν : Int, ν = x - 1 →
        ∃ ν', ν' = x - 1 ∧ ν = ν' := by
  grind

theorem ex1_kappa_soundness :
    ∀ x : Int, 0 ≤ x →
      ∀ y : Int, (∃ ν', ν' = x - 1 ∧ y = ν') →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν := by
  grind
