import LeanFixpoint

/-
(constant magic (func 0 (int int ) bool))
(define_fun c0 ((a0 int)) bool ((and (and (and (magic 0 a0) (magic 1 a0)) (magic 2 a0)) (magic 3 a0))))
(define_fun c1 ((a1 int)) bool ((or (or (or (= 0 a1) (= 1 a1)) (= 2 a1)) (= 3 a1))))

(constraint
 (forall ((n0 int) (true))
  (forall ((_$ int) ((and (and (and (magic 0 n0) (magic 1 n0)) (magic 2 n0)) (magic 3 n0))))
   (tag ((magic 3 n0)) "0"))))
-/
-- c0 a0 := magic0 a0 ∧ magic1 a0 ∧ magic2 a0 ∧ magic3 a0
-- c1 a1 := a1 = 0 ∨ a1 = 1 ∨ a1 = 2 ∨ a1 = 3  (unused in constraint)

def lhDefineFun01Prop
    (magic0 magic1 magic2 magic3 : Int → Prop) : Prop :=
  ∀ n0 : Int, True →
    ∀ _x : Int,
      (magic0 n0 ∧ magic1 n0 ∧ magic2 n0 ∧ magic3 n0) →
        magic3 n0

theorem lhDefineFun01Proof :
    ∀ magic0 magic1 magic2 magic3 : Int → Prop,
    lhDefineFun01Prop magic0 magic1 magic2 magic3 := by
  solve_fixpoint
