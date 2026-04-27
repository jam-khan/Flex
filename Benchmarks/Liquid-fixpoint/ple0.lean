import LeanFixpoint
/-
(fixpoint "--rewrite")

(constant adder (func 0 (Int Int) Int))

(define adder ((x Int) (y Int)) Int (+ x y))


(constraint
  (and
    (forall ((x Int) ((= x 5)))
      (forall ((y Int) ((= y 6)))
        ((= ((adder x) y) 11))))))
-/
def adder (x y : Int) : Int := x + y

def adderProp : Prop :=
  ∀ x : Int, x = 5 → ∀ y : Int, y = 6 → adder x y = 11

theorem adderProof : adderProp := by
  solve_fixpoint  -- unfolds adder, omega closes
