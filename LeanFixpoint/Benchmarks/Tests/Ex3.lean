import LeanFixpoint.Tactic.Command


/-!
  # Example 3 — Higher-Order Composition (Local Refinement Typing, §2)

  ```
  ex3 :: Nat → Nat
  ex3 = let fn = \a -> dec a
            fp = \b -> inc b
        in fp . fn
  ```

  Templates:
    fn     :: {a | κa(a)} → {v | κb(v)}
    fp     :: {b | κb(b)} → {v | κc(v)}
    fp . fn :: {a | κa(a)} → {v | κc(v)}

  Constraints:
    (10) ∀a. κa(a)  ⇒ ∀ν. ν = a-1 ⇒ κb(ν)   — body of fn
    (11) ∀b. κb(b)  ⇒ ∀ν. ν = b+1 ⇒ κc(ν)   — body of fp
    (12) ∀ν. 0 ≤ ν  ⇒ κa(ν)                  — Nat input
    (13) ∀ν. κc(ν)  ⇒ 0 ≤ ν                  — Nat output

  Elimination order: κa → κb → κc
    κa(z) ≈ 0 ≤ z
    κb(z) ≈ 0 ≤ z + 1
    κc(z) ≈ 0 ≤ z
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

#solve_constraint ex3Constraint
