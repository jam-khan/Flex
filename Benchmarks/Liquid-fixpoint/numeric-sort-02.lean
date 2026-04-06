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

def qualifiers02 : List Qualifier := [
  q{ Bar(v : int, z : int) | v ≥ z }
]

def numericSort02Prop : Prop :=
  ∃ κ1 : Int → Int → Prop,
    ∀ zero : Int, zero = 0 →
      -- Base: n ≤ zero ⇒ VV = zero ⇒ κ1(VV, zero)
      (∀ n : Int, n ≤ zero → ∀ VV : Int, VV = zero → κ1 VV zero)
      -- Rec: 0 < n ⇒ n1 = n-1 ⇒ κ1(t1, zero) ⇒ v = n+t1 ⇒ κ1(v, zero)
      ∧ (∀ n : Int, 0 < n → ∀ n1 : Int, n1 = n - 1 →
          ∀ t1 : Int, κ1 t1 zero → ∀ v : Int, v = n + t1 → κ1 v zero)
      -- Use: κ1(r, zero) ⇒ zero ≤ r
      ∧ (∀ y : Int, ∀ r : Int, κ1 r zero → zero ≤ r)

theorem numericSort02Proof : numericSort02Prop := by
  solve_fixpoint with qualifiers02
  
  sorry
