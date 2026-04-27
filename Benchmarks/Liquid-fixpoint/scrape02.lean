/-
(fixpoint "--scrape=both")

(datatype (Adt0 0) ((mkadt0$0 ()) (mkadt0$1 ())))
(datatype (Adt1 0) ((mkadt1$0 ((fld1$0 int) (fld1$1 int)))))

(constant f$get_mode$0 (func 0 ((BitVec Size32) int ) (Adt0)))  ;; flux def: FluxId { parent: DefId(0:230 ~ flux_demo[a644]::typestate_addr), name: "get_mode" }

(var $k0 (int (BitVec Size32) int)) ;; orig: $k5
(var $k1 (int int int (BitVec Size32) int)) ;; orig: $k0
(var $k2 (int int (BitVec Size32) int)) ;; orig: $k0
(var $k3 (int (BitVec Size32) int)) ;; orig: $k0
(var $k4 (int int int int (BitVec Size32) int)) ;; orig: $k2
(var $k5 (int (BitVec Size32) int int int int)) ;; orig: $k6

(constraint
 (forall ((reftgen$modes$0 (BitVec Size32)) (true))
  (forall ((a0 int) (true))
   (forall ((_$ int) (true))
    (forall ((_$ int) (true))
     (and
      (forall ((a1 int) (true))
       (forall ((_$ int) (((= (f$get_mode$0 reftgen$modes$0 a1) (mkadt0$0 )))))
         ($k0 a1 reftgen$modes$0 a0)))
      (forall ((a4 int) (true))
       (forall ((_$ int) ($k0 a4 reftgen$modes$0 a0))
        (forall ((a5 int) (true))
         (forall ((a6 int) (true))
          ($k4 a4 a5 a6 a0 reftgen$modes$0 a0)))))
      (forall ((a7 int) (true))
       (forall ((a8 (Adt1)) (true))
        (forall ((a9 int) (true))
         (forall ((a10 int) (true))
          (forall ((_$ int) (and ($k1 a7 a9 a10 reftgen$modes$0 a0) ($k2 a9 a10 reftgen$modes$0 a0) ($k3 a10 reftgen$modes$0 a0)))
           (and
            (forall ((a11 int) (true))
             (forall ((a12 int) (true))
              (forall ((a13 int) (true))
               (forall ((_$ int) ($k4 a11 a7 a12 a13 reftgen$modes$0 a0))
                (forall ((a14 int) (true))
                 (forall ((a15 int) (true))
                  ($k5 a11 reftgen$modes$0 a0 a7 a14 a15)))))))
            (forall ((a16 (Adt1)) (true))
               (forall ((a17 int) (true))
                (forall ((a18 int) (true))
                 (forall ((a19 int) (true))
                  (forall ((_$ int) ($k5 a17 reftgen$modes$0 a0 a7 a18 a19))
                    (and
                     (tag ((= (f$get_mode$0 reftgen$modes$0 a17) (mkadt0$0 ))) "1")
                     (forall ((a20 bool) (true))
                       (and
                        (forall ((a21 int) (true))
                         (forall ((a22 int) (true))
                          (forall ((a23 int) (true))
                           (and
                            ($k1 a21 a22 a23 reftgen$modes$0 a0)
                            ($k2 a22 a23 reftgen$modes$0 a0)
                            ($k3 a23 reftgen$modes$0 a0)))))
                        (forall ((a24 int) (true))
                         (forall ((a25 int) (true))
                          (forall ((a26 int) (true))
                           (forall ((_$ int) ($k5 a24 reftgen$modes$0 a0 a7 a25 a26))
                            (forall ((a27 int) (true))
                             (forall ((a28 int) (true))
                              (forall ((a29 int) (true))
                               ($k4 a24 a27 a28 a29 reftgen$modes$0 a0))))))))))
                               ))))))))))))))))))
-/

import LeanFixpoint

-- (datatype (Adt0 0) ((mkadt0$0 ()) (mkadt0$1 ())))
@[grind]
inductive Adt0 : Type where
  | mkadt0_0
  | mkadt0_1
  deriving Nonempty


-- (datatype (Adt1 0) ((mkadt1$0 ((fld1$0 int) (fld1$1 int)))))
@[grind]
structure Adt1 : Type where
  mk ::
  fld1_0 : Int
  fld1_1 : Int

-- (constant f$get_mode$0 (func 0 ((BitVec Size32) int) (Adt0)))
-- (constant f$get_mode$0 (func 0 ((BitVec Size32) int) (Adt0)))
@[simp]
def f_get_mode (_m : BitVec 32) (_a : Int) : Adt0 := Adt0.mkadt0_0

@[qualif] def q_zero (a : Int) : Prop := a = 0
@[qualif] def q_eq_mode (a : Int) (m : BitVec 32) : Prop :=
  f_get_mode m a = Adt0.mkadt0_0

def scrape02 : Prop :=
  ∃ k0 : Int → BitVec 32 → Int → Prop,
  ∃ k1 : Int → Int → Int → BitVec 32 → Int → Prop,
  ∃ k2 : Int → Int → BitVec 32 → Int → Prop,
  ∃ k3 : Int → BitVec 32 → Int → Prop,
  ∃ k4 : Int → Int → Int → Int → BitVec 32 → Int → Prop,
  ∃ k5 : Int → BitVec 32 → Int → Int → Int → Int → Prop,
    ∀ reftgen : BitVec 32, ∀ a0 : Int,
      -- Seed:  f_get_mode reftgen a1 = mkadt0_0  →  k0 a1 reftgen a0
      (∀ a1 : Int,
          f_get_mode reftgen a1 = Adt0.mkadt0_0 → k0 a1 reftgen a0)
    ∧ -- k0 → k4
      (∀ a4 : Int, k0 a4 reftgen a0 →
          ∀ a5 a6 : Int, k4 a4 a5 a6 a0 reftgen a0)
    ∧ -- Main consumer
      (∀ a7 : Int, ∀ _a8 : Adt1, ∀ a9 a10 : Int,
          (k1 a7 a9 a10 reftgen a0 ∧ k2 a9 a10 reftgen a0 ∧ k3 a10 reftgen a0) →
            -- Sub-A: k4 → k5
            (∀ a11 a12 a13 : Int, k4 a11 a7 a12 a13 reftgen a0 →
                ∀ a14 a15 : Int, k5 a11 reftgen a0 a7 a14 a15)
          ∧
            -- Sub-B: k5 → (check ∧ bool branching)
            (∀ _a16 : Adt1, ∀ a17 a18 a19 : Int,
                k5 a17 reftgen a0 a7 a18 a19 →
                  -- Check (the (tag …) clause)
                  f_get_mode reftgen a17 = Adt0.mkadt0_0
                ∧
                  (∀ _a20 : Bool,
                      -- Re-seed k1, k2, k3
                      (∀ a21 a22 a23 : Int,
                          k1 a21 a22 a23 reftgen a0
                        ∧ k2 a22 a23 reftgen a0
                        ∧ k3 a23 reftgen a0)
                    ∧
                      -- k5 → k4
                      (∀ a24 a25 a26 : Int, k5 a24 reftgen a0 a7 a25 a26 →
                          ∀ a27 a28 a29 : Int, k4 a24 a27 a28 a29 reftgen a0))))

set_option maxHeartbeats 6400000 in
theorem scrape02_proof : scrape02 := by
  try solve_fixpoint
  sorry
