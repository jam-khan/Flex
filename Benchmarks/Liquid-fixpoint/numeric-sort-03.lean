import LeanFixpoint
/-

(numeric Apple)
(numeric Banana)

(qualif Bar ((v @(0)) (z @(1))) (>= (cast v Int) (cast z Int)))

(var $k1 (Apple Banana))

(constraint
  (and
    (forall ((zero Banana) ((= zero 0)))
      (and
        (forall ((n Apple) (true))
          (forall ((cond bool) ((<=> cond (<= n zero))))
            (and
              (forall ((grd bool) (cond))
                (forall ((VV Apple) ((= VV (cast zero Int))))
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

def k1_ns02 : KVar := { name := `κ1, params := [`v, `z] }

def lhNumericSort02 : Constraint :=
  c{ ∀ zero : int . zero == 0 ⇒
        [∀ n : int . n ≤ zero ⇒
          ∀ VV : int . VV == zero ⇒ k1_ns02(VV, zero)]
      ∧ [∀ n : int . 0 < n ⇒
          ∀ n1 : int . n1 == n - 1 ⇒
            ∀ t1 : int . k1_ns02(t1, zero) ⇒
              ∀ v : int . v == n + t1 ⇒ k1_ns02(v, zero)]
      ∧ [∀ y : int . true ⇒
          ∀ r : int . k1_ns02(r, zero) ⇒ zero ≤ r] }

-- #solve_constraint_full lhNumericSort02 with [{ pred := r{ v ≥ 0 } }]
