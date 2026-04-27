import LeanFixpoint
/-
(fixpoint "--rewrite")

(constant sum (func 0 (Int) Int))

(define sum ((n Int)) Int (if (<= n 0) 0 (+ n (sum (- n 1)))))

(constraint
  (and
    (forall ((x Int) ((= x 5)))
      ((= (sum x) 15)))))
-/

@[grind, simp]
def mySum (n : Int) : Int :=
  if n ≤ 0 then 0 else n + mySum (n - 1)
termination_by n.toNat

def pleSumProp : Prop :=
  ∀ x : Int, x = 5 → mySum x = 15

set_option maxRecDepth 2000 in
theorem pleSumProof : pleSumProp := by
  -- solve_fixpoint
  unfold pleSumProp
  simp_all [mySum]
