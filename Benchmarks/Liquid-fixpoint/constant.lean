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

import LeanFixpoint

def constantProp (f : Int → Int) : Prop :=
  ∃ κ0 : Int → Prop,
    ∀ x : Int, x > 0 →
      (∀ v : Int, v = f x → κ0 v)
      ∧ (∀ z : Int, κ0 z → z = f x)

theorem constantProof (f : Int → Int) : constantProp f := by sorry
