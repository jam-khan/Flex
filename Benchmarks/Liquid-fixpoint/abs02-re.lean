import LeanFixpoint
/-
  Liquid Haskell test
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/abs02-re.smt2`

  (constraint
  (and
    (and
      (forall ((x Int) (true))
        (forall ((VV Int) ((= VV 10)))
          ((>= VV 0))))
      (forall ((z Int) (true))
        (and
          (forall ((r Int) ((>= r 0)))
            (forall ((v Int) ((and (= v r) (>= v 0))))
              ((>= v 0))))
          (forall ((_t1 Int) ((>= _t1 0)))
            (forall ((v Int) ((>= v 0)))
              ((>= v 0)))))))))
-/

-- Old c{...} macro syntax — commented out, uses `==` which is no longer supported
-- def lhGround : Constraint :=
--   c{  [∀ x : int . true ⇒
--         ∀ VV : int . VV == 10 ⇒ VV ≥ 0]
--     ∧ [∀ z : int . true ⇒
--         ∀ r : int . r ≥ 0 ⇒
--           ∀ v : int . v == r ∧ v ≥ 0 ⇒ v ≥ 0]
--     ∧ [∀ z : int . true ⇒
--         ∀ t1 : int . t1 ≥ 0 ⇒
--           ∀ v : int . v ≥ 0 ⇒ v ≥ 0] }
-- #solve_constraint lhGround

def lhGroundProp : Prop :=
  (∀ x : Int, True →
    ∀ VV : Int, VV = 10 →
      0 ≤ VV)
  ∧ (∀ z : Int, True →
      (∀ r : Int, 0 ≤ r →
        ∀ v : Int, v = r ∧ 0 ≤ v →
          0 ≤ v)
      ∧ (∀ t1 : Int, 0 ≤ t1 →
          ∀ v : Int, 0 ≤ v →
            0 ≤ v))

theorem lhGroundProof : lhGroundProp := by
  solve_fixpoint
