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

-- cast erased: Apple, Banana both map to Int
-- def qBar03 : Qualifier :=
def qualifiers : List Qualifier := [
  q{ Bar(v : int, z : int) | v ≥ z }
]

def numericSort03Prop : Prop :=
  ∃ κ1 : Int → Int → Prop,
    ∀ zero : Int, zero = 0 →
      (∀ n : Int, n ≤ zero → ∀ VV : Int, VV = zero → κ1 VV zero)
      ∧ (∀ n : Int, 0 < n → ∀ n1 : Int, n1 = n - 1 →
          ∀ t1 : Int, κ1 t1 zero → ∀ v : Int, v = n + t1 → κ1 v zero)
      ∧ (∀ y : Int, ∀ r : Int, κ1 r zero → zero ≤ r)

theorem numericSort03Proof : numericSort03Prop := by

  sorry
