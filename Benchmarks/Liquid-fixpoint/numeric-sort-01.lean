import LeanFixpoint
/-

(numeric Apple)

(qualif Bar ((v @(0))) (>= v 0))

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

def qBar01 : Qualifier := q{ Bar(v : int) | 0 ≤ v }

def numericSort01Prop : Prop :=
  ∃ κ1 : Int → Prop,
    -- Base: n ≤ 0 ⇒ VV = 0 ⇒ κ1(VV)
    (∀ n : Int, n ≤ 0 → ∀ VV : Int, VV = 0 → κ1 VV)
    -- Rec: 0 < n ⇒ n1 = n-1 ⇒ κ1(t1) ⇒ v = n+t1 ⇒ κ1(v)
    ∧ (∀ n : Int, 0 < n → ∀ n1 : Int, n1 = n - 1 →
        ∀ t1 : Int, κ1 t1 → ∀ v : Int, v = n + t1 → κ1 v)
    -- Use: κ1(r) ⇒ 0 ≤ r
    ∧ (∀ y : Int, ∀ r : Int, κ1 r → 0 ≤ r)

theorem numericSort01Proof : numericSort01Prop := by
  sorry
