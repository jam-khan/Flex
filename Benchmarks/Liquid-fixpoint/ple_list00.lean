import LeanFixpoint
/-
(fixpoint "--rewrite")

(constant len (func 1 ((MyList @(0))) Int))
(constant Cons (func 2 (@(0) (MyList @(0))) (MyList @(0))))
(constant Nil (MyList @(0)))

(match len (Nil) 0)
(match len (Cons x xs) (+ 1 (len xs)))

(constraint
  (and
    (forall ((x Int) (true))
      (forall ((y Int) ((= y 2)))
        (forall ((z Int) ((= z 3)))
          ((= (len ((Cons x) ((Cons y) ((Cons z) Nil)))) 3)))))))
-/

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

def myLen : MyList α → Int
  | .nil       => 0
  | .cons _ xs => 1 + myLen xs

def ple1Prop : Prop :=
  ∀ x : Int, True → ∀ y : Int, y = 2 → ∀ z : Int, z = 3 →
    myLen (MyList.cons x (MyList.cons y (MyList.cons z MyList.nil))) = 3

theorem ple1Proof : ple1Prop := by
  solve_fixpoint
