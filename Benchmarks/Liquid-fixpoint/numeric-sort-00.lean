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

def kApple : KVar := { name := `κ1, params := [`v] }

def lhAppleSum : Constraint :=
  c{  -- Base: n ≤ 0 ⇒ VV = 0 ⇒ κ1(VV)
      [∀ n : int . n ≤ 0 ⇒
        ∀ VV : int . VV == 0 ⇒ kApple(VV)]
      -- Rec: ¬(n ≤ 0) ⇒ n1 = n-1 ⇒ κ1(t1) ⇒ v = n+t1 ⇒ κ1(v)
    ∧ [∀ n : int . 0 < n ⇒
        ∀ n1 : int . n1 == n - 1 ⇒
          ∀ t1 : int . kApple(t1) ⇒
            ∀ v : int . v == n + t1 ⇒ kApple(v)]
      -- Use: κ1(r) ⇒ 0 ≤ r
    ∧ [∀ y : int . true ⇒
        ∀ r : int . kApple(r) ⇒ 0 ≤ r] }

-- #solve_constraint_full lhAppleSum with [{ pred := r{ 0 ≤ v } }]
