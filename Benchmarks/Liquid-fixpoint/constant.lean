/-


(qualif Foo ((v Int)) (> v 100))

(var $k0 (Int))

(constant f (func 0 (Int) Int))




(constraint
  (and
    (forall ((x Int) ((> x 0)))
      (and
        (forall ((v Int) ((= v (f x))))
          ($k0 v))
        (forall ((z Int) ($k0 z))
          ((= z (f x))))))))
-/

-- need to let kappa have access to sufficient scope

import LeanFixpoint

def constantProp : Prop :=
  ∀ f : Int → Int,
    ∃ κ0 : Int → Int → Prop,
      ∀ x : Int, x > 0 →
        (∀ v : Int, v = f x → κ0 v x)
        ∧ (∀ z : Int, κ0 z x → z = f x)


theorem constantProof : constantProp := by
  solve_fusion
