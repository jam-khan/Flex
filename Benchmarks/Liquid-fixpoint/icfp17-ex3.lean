import LeanFixpoint
/-
(fixpoint "--eliminate=horn")



(var $ka (Int))
(var $kb (Int))
(var $kc (Int))





(constraint
  (and
    (and
      (forall ((a Int) ($ka a))
        (forall ((v Int) ((= v (- a 1))))
          ($kb v)))
      (forall ((b Int) ($kb b))
        (forall ((v Int) ((= v (+ b 1))))
          ($kc v)))
      (forall ((v Int) ((>= v 0)))
        ($ka v))
      (forall ((v Int) ($kc v))
        ((>= v 0))))))
-/

def icfp17Ex3Prop : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ v : Int, v = a - 1 → κb v)
    ∧ (∀ b : Int, κb b → ∀ v : Int, v = b + 1 → κc v)
    ∧ (∀ v : Int, 0 ≤ v → κa v)
    ∧ (∀ v : Int, κc v → 0 ≤ v)

theorem icfp17Ex3Proof : icfp17Ex3Prop := by
  solve_fixpoint

