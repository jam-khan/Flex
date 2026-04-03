import LeanFixpoint
/-
(numeric Apple)

(qualif Bar ((v @(0)) (z @(1))) (>= v z))

(var $k1 (Apple Int))

(constraint
  (and
    (forall ((zero Int) ((= zero 0)))
      (and
        (forall ((n Apple) (true))
          (forall ((cond bool) ((<=> cond (<= n zero))))
            (and
              (forall ((grd bool) (cond))
                (forall ((VV Apple) ((= VV zero)))
                  ($k1 VV zero)))
              (forall ((grd bool) ((not cond)))
                (forall ((n1 Apple) ((= n1 (- n 1))))
                  (forall ((t1 Apple) ($k1 t1 zero))
                    (forall ((v Apple) ((= v (+ n t1))))
                      ($k1 v zero))))))))
        (forall ((y Apple) (true))
          (forall ((r Apple) ($k1 r zero))
            (forall ((ok1 bool) ((<=> ok1 (<= zero r))))
              (forall ((v bool) (and ((<=> v (<= zero r))) ((= v ok1))))
                (v)))))))))
-/

def k1_ns01 : KVar := { name := `κ1, params := [`v, `z] }

def lhNumericSort01 : Constraint :=
  c{  -- zero = 0 is bound at the top
      ∀ zero : int . zero == 0 ⇒
        -- Base: n ≤ zero ⇒ VV = zero ⇒ κ1(VV, zero)
        [∀ n : int . n ≤ zero ⇒
          ∀ VV : int . VV == zero ⇒ k1_ns01(VV, zero)]
        -- Rec: ¬(n ≤ zero) ⇒ n1 = n-1 ⇒ κ1(t1, zero) ⇒ v = n+t1 ⇒ κ1(v, zero)
      ∧ [∀ n : int . 0 < n ⇒
          ∀ n1 : int . n1 == n - 1 ⇒
            ∀ t1 : int . k1_ns01(t1, zero) ⇒
              ∀ v : int . v == n + t1 ⇒ k1_ns01(v, zero)]
        -- Use: κ1(r, zero) ⇒ zero ≤ r
      ∧ [∀ y : int . true ⇒
          ∀ r : int . k1_ns01(r, zero) ⇒ zero ≤ r] }

-- #solve_constraint_full lhNumericSort01 with [{ pred := r{ v ≥ 0 } }]
