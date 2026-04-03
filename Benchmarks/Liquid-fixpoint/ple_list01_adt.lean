import LeanFixpoint
/-
(fixpoint "--rewrite")

(constant len (func 1 ((Vec @(0))) Int))

(define len ((l (Vec a))) Int (if
                               (is$VNil l)
                               0
                               (+ 1 (len (tail l)))))

(datatype (Vec 1)
 ((VNil ())
  (VCons ((head @(0)) (tail (Vec @(0)))))))


(constraint
  (and
    (forall ((x Int) (true))
      (forall ((y Int) ((= y 2)))
        (forall ((z Int) ((= z 3)))
          ((= (len ((VCons x) ((VCons y) ((VCons z) VNil)))) 3)))))))
-/

inductive Vec (α : Type) where
  | vnil  : Vec α
  | vcons : α → Vec α → Vec α

def vecLen : Vec α → Int
  | .vnil       => 0
  | .vcons _ xs => 1 + vecLen xs

def pleListProp : Prop :=
  ∀ x : Int, True → ∀ y : Int, y = 2 → ∀ z : Int, z = 3 →
    vecLen (Vec.vcons x (Vec.vcons y (Vec.vcons z Vec.vnil))) = 3

theorem pleListProof : pleListProp := by
  solve_fixpoint
