/-
  Liquid Haskell test
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/abs02-re.smt2`
-/
import LeanFixpoint.Tactic.Command

def lhGround : Constraint :=
  c{  [∀ x : int . true ⇒
        ∀ VV : int . VV == 10 ⇒ VV ≥ 0]
    ∧ [∀ z : int . true ⇒
        ∀ r : int . r ≥ 0 ⇒
          ∀ v : int . v == r ∧ v ≥ 0 ⇒ v ≥ 0]
    ∧ [∀ z : int . true ⇒
        ∀ t1 : int . t1 ≥ 0 ⇒
          ∀ v : int . v ≥ 0 ⇒ v ≥ 0] }

-- #solve_constraint lhGround
