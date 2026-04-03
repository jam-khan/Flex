import LeanFixpoint
/-
NOTE: BELOW MUST HAVE A TYPO on kx p

(fixpoint "--eliminate=horn")



(var $kx (Int))
(var $ky (Int))





(constraint
  (and
    (forall ((x Int) ((>= x 0)))
      (and
        (forall ((n Int) ((= n (- x 1))))
          (forall ((p Int) ((= p (+ x 1))))
            (and
              (forall ((v Int) ((= v n)))
                ($kx v))
              (forall ((v Int) ((= v p)))
                ($ky v))
              (forall ((v Int) ($kx p))
                ($ky v)))))
        (forall ((y Int) ($ky y))
          (forall ((v Int) ((= v (+ y 1))))
            ((>= v 0))))))))
-/

def icfp17Ex2Prop : Prop :=
  ∃ κx : Int → Prop, ∃ κy : Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          (∀ v : Int, v = n → κx v)
          ∧ (∀ v : Int, v = p → κy v)
          ∧ (∀ v : Int, κx v → κy v))
      ∧ (∀ y : Int, κy y → ∀ v : Int, v = y + 1 → 0 ≤ v)

theorem icfp17Ex2Proof : icfp17Ex2Prop := by
  solve_fixpoint
