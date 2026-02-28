import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab
-- BELOW is for example 2 of paper

/-
  ex2 constraint from Section 2.3, equations (4)-(7):

  ∀x:int. (0 ≤ x) ⇒
    ∀n:int. (n = x − 1) ⇒
      ∀p:int. (p = x + 1) ⇒
            (∀ν:int. (ν = n) ⇒ κx(ν))                       -- (4)
          ∧ (∀ν:int. (ν = p) ⇒ κy(ν))                       -- (5)
          ∧ (∀ν:int. κx(ν) ⇒ κy(ν))                         -- (6)
          ∧ (∀y:int. κy(y) ⇒ ∀ν:int. (ν = y + 1) ⇒ 0 ≤ ν)  -- (7)
-/

-- Two κ-variables: κx for xs, κy for ys
def kappa_x : KVar := { name := `κx, params := [`z] }
def kappa_y : KVar := { name := `κy, params := [`z] }

def ex2Constraint : Constraint :=
  .imp `x .int
    (.rexpr (.cmp .le (.int 0) (.var `x)))
    (.imp `n .int
      (.rexpr (.mkEq (.var `n) (.arith .sub (.var `x) (.int 1))))
      (.imp `p .int
        (.rexpr (.mkEq (.var `p) (.arith .add (.var `x) (.int 1))))
        (.conj
          (.conj
            (.conj
              -- (4): ∀ν:int. (ν = n) ⇒ κx(ν)
              (.imp `ν .int
                (.rexpr (.mkEq (.var `ν) (.var `n)))
                (.pred (.kapp kappa_x [`ν])))
              -- (5): ∀ν:int. (ν = p) ⇒ κy(ν)
              (.imp `ν .int
                (.rexpr (.mkEq (.var `ν) (.var `p)))
                (.pred (.kapp kappa_y [`ν]))))
            -- (6): ∀ν:int. κx(ν) ⇒ κy(ν)
            (.imp `ν .int
              (.kapp kappa_x [`ν])
              (.pred (.kapp kappa_y [`ν]))))
          -- (7): ∀y:int. κy(y) ⇒ ∀ν:int. (ν = y + 1) ⇒ 0 ≤ ν
          (.imp `y .int
            (.kapp kappa_y [`y])
            (.imp `ν .int
              (.rexpr (.mkEq (.var `ν) (.arith .add (.var `y) (.int 1))))
              (.pred (.rexpr (.cmp .le (.int 0) (.var `ν)))))))))

-- Eliminate κx first (it only flows into κy), then κy
def ex2Eliminated := ex2Constraint.elim [kappa_x, kappa_y]

#eval ex2Eliminated.kvars

-- Below is ideal simplified vc for ex2, we want to
-- see if `grind` or `omega` can handle it

/-
  ex2 final VC after eliminating κx then κy.

  κx(z) ≡ ∃ν. (ν = n) ∧ z = ν
         simplified: z = n, i.e. z = x - 1, so 0 ≤ z + 1

  κy(z) ≡ (∃ν. ν = p ∧ z = ν)          -- from (5)
         ∨ (∃ν. κx(ν) ∧ z = ν)          -- from (6), κx substituted
         simplified: z = x + 1 ∨ (0 ≤ z + 1)
         both imply 0 ≤ z + 1

  Final VC (constraint 7 with κy substituted):
    ∀x. 0 ≤ x →
      ∀n. n = x - 1 →
        ∀p. p = x + 1 →
          ∀y.   (∃ ν', ν' = p ∧ y = ν')
              ∨ (∃ ν', (∃ ν'', ν'' = n ∧ ν' = ν'') ∧ y = ν')
              → ∀ν. ν = y + 1 → 0 ≤ ν
-/
theorem ex2_vc :
    ∀ x : Int, 0 ≤ x →
      ∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          ∀ y : Int,
            -- κy(y): disjunction from (5) and (6)
            ((∃ ν', ν' = p ∧ y = ν')
            ∨ (∃ ν', (∃ ν'', ν'' = n ∧ ν' = ν'') ∧ y = ν'))
            → ∀ ν : Int, ν = y + 1 → 0 ≤ ν := by
  grind
