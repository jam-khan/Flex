import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Macros

/-
  **Example 3**
```
  ex3 :: Nat → Nat
  ex3 = let fn = \a -> dec a
            fp = \b -> inc b
        in fp . fn
```
-/

/-
  Step 1: Generate Templates

    fn :: {a : Int | κa(a)} → {v : Int | κb(v)}
    fp :: {b : Int | κb(b)} → {v : Int | κc(v)}
    fp . fn :: {a : Int | κa(a)} → {v : Int | κc(v)}

    κa, κb, κc are fresh refinement variables
    instantiated from the type variables a, b, c of (.)

  Step 2: Generate Constraints

    ∀a. κa(a) ⇒ ∀ν. ν = a - 1 ⇒ κb(ν)   (10)
    ∀b. κb(b) ⇒ ∀ν. ν = b + 1 ⇒ κc(ν)   (11)
    ∀ν. 0 ≤ ν ⇒ κa(ν)                    (12)
    ∀ν. κc(ν) ⇒ 0 ≤ ν                    (13)

    (10): body of fn must match κb template
    (11): body of fp must match κc template
    (12): input to ex3 is Nat, so {v | 0 ≤ v} <: {v | κa(v)}
    (13): output of ex3 must be Nat, so {v | κc(v)} <: {v | 0 ≤ v}

  Step 3: Solution

    Eliminate κa, κb, κc in dependency order: κa → κb → κc

    κa(z) ≡ ∃ν. 0 ≤ ν ∧ z = ν
           simplified: 0 ≤ z

    κb(z) ≡ ∃a. κa(a) ∧ ∃ν. ν = a - 1 ∧ z = ν
           simplified: 0 ≤ z + 1

    κc(z) ≡ ∃b. κb(b) ∧ ∃ν. ν = b + 1 ∧ z = ν
           simplified: 0 ≤ z

    Substituting into (13): 0 ≤ z ⇒ 0 ≤ z  ✓
-/

def kappa_a : KVar := { name := `κa, params := [`z] }
def kappa_b : KVar := { name := `κb, params := [`z] }
def kappa_c : KVar := { name := `κc, params := [`z] }

def ex3Constraint : Constraint :=
  c{  [∀ a : int . kappa_a(a) ⇒ ∀ ν : int . ν == a - 1 ⇒ kappa_b(ν)]
    ∧ [∀ b : int . kappa_b(b) ⇒ ∀ ν : int . ν == b + 1 ⇒ kappa_c(ν)]
    ∧ [∀ ν : int . 0 ≤ ν ⇒ kappa_a(ν)]
    ∧ [∀ ν : int . kappa_c(ν) ⇒ 0 ≤ ν] }

def ex3Eliminated := ex3Constraint.elim [kappa_a, kappa_b, kappa_c]

#eval ex3Constraint.kvars
#eval ex3Eliminated.kvars

-- κa justified by (12): Nat input flows into κa
theorem ex3_kappa_a_solution :
    ∀ ν : Int, 0 ≤ ν →
      ∃ ν', ν' = ν ∧ 0 ≤ ν' := by
  grind

-- κb justified by (10): κa flows into κb via dec
theorem ex3_kappa_b_solution :
    ∀ a : Int, 0 ≤ a →
      ∀ ν : Int, ν = a - 1 →
        ∃ a', 0 ≤ a' ∧ ∃ ν', ν' = a' - 1 ∧ ν = ν' := by
  grind

-- κc justified by (11): κb flows into κc via inc
theorem ex3_kappa_c_solution :
    ∀ b : Int,
      (∃ a, 0 ≤ a ∧ ∃ ν', ν' = a - 1 ∧ b = ν') →
      ∀ ν : Int, ν = b + 1 →
        ∃ b', (∃ a, 0 ≤ a ∧ ∃ ν', ν' = a - 1 ∧ b' = ν') ∧
              ∃ ν'', ν'' = b' + 1 ∧ ν = ν'' := by
  grind

-- Final VC (13): κc's solution implies 0 ≤ ν
theorem ex3_kappa_soundness :
    ∀ ν : Int,
      (∃ b, (∃ a, 0 ≤ a ∧ ∃ ν', ν' = a - 1 ∧ b = ν') ∧
            ∃ ν'', ν'' = b + 1 ∧ ν = ν'') →
      0 ≤ ν := by
  grind

