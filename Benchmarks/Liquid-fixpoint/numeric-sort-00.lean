import LeanFixpoint
/-
(numeric Apple)

(qualif Bar ((v Apple)) (>= v 0))

(var $k1 (Apple))

(constraint
  (and
    (and
      (forall ((n Apple) (true))
        (forall ((cond bool) ((<=> cond (<= n 0))))
          (and
            (forall ((grd bool) (cond))
              (forall ((VV Apple) ((= VV 0)))
                ($k1 VV)))
            (forall ((grd bool) ((not cond)))
              (forall ((n1 Apple) ((= n1 (- n 1))))
                (forall ((t1 Apple) ($k1 t1))
                  (forall ((v Apple) ((= v (+ n t1))))
                    ($k1 v))))))))
      (forall ((y Apple) (true))
        (forall ((r Apple) ($k1 r))
          (forall ((ok1 bool) ((<=> ok1 (<= 0 r))))
            (forall ((v bool) (and ((<=> v (<= 0 r))) ((= v ok1))))
              (v))))))))
-/
@[qualif] def q_eq_zero (v : Int)   : Prop := v = 0
@[qualif] def q_gt_zero (v : Int)   : Prop := 0 < v
@[qualif] def q_ge_zero (v : Int)   : Prop := 0 ≤ v
@[qualif] def q_lt_zero (v : Int)   : Prop := v < 0
@[qualif] def q_le_zero (v : Int)   : Prop := v ≤ 0
@[qualif] def q_eq      (a b : Int) : Prop := a = b
@[qualif] def q_gt      (a b : Int) : Prop := a > b
@[qualif] def q_ge      (a b : Int) : Prop := a ≥ b
@[qualif] def q_lt      (a b : Int) : Prop := a < b
@[qualif] def q_le      (a b : Int) : Prop := a ≤ b
@[qualif] def q_le1     (a b : Int) : Prop := a ≤ b - 1


def numericSort00Prop : Prop :=
  ∃ κ1 : Int → Prop,
    (∀ n : Int, n ≤ 0 → ∀ VV : Int, VV = 0 → κ1 VV)
    ∧ (∀ n : Int, 0 < n → ∀ n1 : Int, n1 = n - 1 →
        ∀ t1 : Int, κ1 t1 → ∀ v : Int, v = n + t1 → κ1 v)
    ∧ (∀ y : Int, ∀ r : Int, κ1 r → 0 ≤ r)

theorem numericSort00Proof : numericSort00Prop := by
  solve_fixpoint
