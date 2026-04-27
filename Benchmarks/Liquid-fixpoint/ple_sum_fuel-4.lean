/-
SAME AS ple_sum.lean but with fuel which is not needed in lean4

(fixpoint "--rewrite")
(fixpoint "--interpreter=false")
(fixpoint "--fuel=4")




(constant sum (func 0 (Int) Int))

(define sum ((n Int)) Int (if (<= n 0) 0 (+ n (sum (- n 1)))))



(constraint
  (and
    (forall ((x Int) ((and (<= 0 (sum (- x 5))) (<= 5 x))))
      ((<= 15 (sum x))))))

-/

import LeanFixpoint

@[grind]
def mySum (n : Int) : Int :=
  if n ≤ 0 then 0 else n + mySum (n - 1)
termination_by n.toNat

@[simp]
def pleSumFuel4Prop : Prop :=
  ∀ x : Int, 0 ≤ mySum (x - 5) → 5 ≤ x → 15 ≤ mySum x

-- needs much more automation due to bounded x ≤ 5
theorem pleSumFuel4Proof : pleSumFuel4Prop := by
  solve_fixpoint
