import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab

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
-/


/-
  Step 2: Generate Constraints

-/

def kappa : KVar := { name := `κ, params := [`z] }

/-
  ex1 constraint from Section 2.3, equations (1) and (2):

    ∀x:int. (0 ≤ x) ⇒
     (∀ν:int. (ν = x − 1) ⇒ κ(ν))                   -- (1)
    ∧ (∀y:int. κ                                           (y) ⇒ ∀ν:int. (ν = y + 1) ⇒ 0 ≤ ν)  -- (2)
-/
def ex1Constraint : Constraint :=
  .imp `x .int
    (.rexpr (.cmp .le (.int 0) (.var `x)))
    (.conj
      (.imp `ν .int
        (.rexpr (.mkEq (.var `ν) (.arith .sub (.var `x) (.int 1))))
        (.pred (.kapp kappa [`ν])))
      (.imp `y .int
        (.kapp kappa [`y])
        (.imp `ν .int
          (.rexpr (.mkEq (.var `ν) (.arith .add (.var `y) (.int 1))))
          (.pred (.rexpr (.cmp .le (.int 0) (.var `ν)))))))

def ex1Eliminated := ex1Constraint.elim1 kappa

-- Below is apparently wrong, it doesn't eliminates single
-- κ variable
#eval ex1Eliminated.kvars


/-
  Below shows the result of the elim + elaboration to
  an actual lean term. Ofc, below is written in terms
  of Lean.Syntax which is the surface level syntax, but
  elaboration will (most likely) target Lean.Expr which
  is the Lean Core.

  Basically,
  Constraint ~> elim1 + elaboration ~> ex1_vc_unsimplified
-/

theorem ex1_vc_unsimplified :
    ∀ x : Int, 0 ≤ x →
      ∀ y : Int, (∃ x', 0 ≤ x' ∧ ∃ ν', ν' = x' - 1 ∧ y = ν') →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν := by
  -- Good news! Grind solves it
  grind
