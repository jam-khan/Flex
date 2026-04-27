import LeanFixpoint
/-
; (fixpoint "--eliminate=horn")

(qualif Foo ((v Int)) (= v 10))
(qualif Foo ((v Int)) (= v 20))
(qualif Foo ((v Int)) (= v 30))

(var $k1 (Int))

(cut $k1)

(constraint
  (and
    (forall ((x Int) ((= x 5)))
      (forall ((y Int) ((= y x)))
        (forall ((v Int) ((= v (+ x y))))
          ($k1 v))))
    (forall ((z Int) ($k1 z))
      ((< 99 105))) ;; silly constraint to make sure $k1 doesn't get "sliced out"
  )
)
-/

def kut00Prop : Prop :=
  ∃ κ1 : Int → Prop,
    (∀ x : Int, x = 5 →
      ∀ y : Int, y = x →
        ∀ v : Int, v = x + y → κ1 v)
    ∧ (∀ z : Int, κ1 z → 99 < 105)

theorem kut00Proof : kut00Prop := by
  solve_fixpoint
