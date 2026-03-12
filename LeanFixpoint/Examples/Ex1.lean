import LeanFixpoint.Constraint
import LeanFixpoint.Elab
import LeanFixpoint.Syntax
import LeanFixpoint.Macros

/-!
  # Example 1 — Local Refinement Typing

  ```
  ex1 :: Nat → Nat
  ex1 x =
    let y =
      let t = x
      in dec t
    in inc y
  ```

  ## Step 1: Generate Templates

    x     :: {v : Int | v ≥ 0}
    t     :: {v : Int | v = x}
    dec t :: {v : Int | v = t - 1}
    y     :: {v : Int | κ(v)}       ← fresh refinement variable
    inc y :: {v : Int | v = y + 1}

  ## Step 2: Generate Constraints (NNF Horn Clause)

    ∀ x : Int. 0 ≤ x ⇒
      (∀ ν : Int. ν = x - 1 ⇒ κ(ν))            — (1) definition
    ∧ (∀ y : Int. κ(y) ⇒ ∀ ν : Int. ν = y + 1 ⇒ 0 ≤ ν) — (2) use

  ## Step 3: Solve & Eliminate κ

    The scoped strongest solution (Section 5.2):
      κ(z) = ∃ ν : Int. (ν = x - 1 ∧ z = ν)

    After elimination (Section 5.3):
    - Head occurrence κ(ν) in (1) → ⊤
    - Body occurrence κ(y) in (2) → ∃ ν. (ν = x - 1 ∧ y = ν)

  ## Step 4: Discharge VC with grind
-/

-- ────────────────────────────────────────────
-- Definition
-- ────────────────────────────────────────────

def kappa : KVar := { name := `κ, params := [`z] }

def ex1Constraint : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒
      [∀ ν : int . ν == x - 1 ⇒ kappa(ν)]
    ∧ [∀ y : int . kappa(y) ⇒
        ∀ ν : int . ν == y + 1 ⇒ 0 ≤ ν] }
#solve_constraint ex1Constraint

def ex1Eliminated := ex1Constraint.elim1 kappa

#eval IO.println (toString ex1Eliminated)

-- Solve: compute strongest scoped solution
#eval do
  let sc := ex1Constraint.scope kappa
  let c' := stripScope kappa sc
  let sol := c'.sol1 kappa
  -- κ(z) = ∃ ν : Int. (ν == x - 1 ∧ z == ν)
  IO.println s!"κ(z) = {toString sol}"

/-
  ∀ x : Int.
    0 <= x
    ⇒ ∀ ν : Int.
      ν == x - 1
      ⇒ ⊤
    ∧ ∀ y : Int.
      ∃ ν : Int. (ν == x - 1 ∧ y == ν)
      ⇒ ∀ ν : Int.
        ν == y + 1
        ⇒ 0 <= ν
-/



-- Manual proofs (for reference / sanity check)
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
