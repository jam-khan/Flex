/-
(constraint
  (and

    (forall ((x Int) ((= x 1)))
      (forall ((y Int) ((= y 2)))
        (forall ((x_ (BitVec Size8)) ((= x_ (int_to_bv8 x))))
          (forall ((y_ (BitVec Size8)) ((= y_ (int_to_bv8 y))))
            (forall ((res_ (BitVec Size8)) ((= res_ (bvadd x_ y_))))
              ((= (bv8_to_int res_) 3)))))))

    (forall ((x Int) ((= x 1)))
      (forall ((y Int) ((= y 2)))
        (forall ((x_ (BitVec Size16)) ((= x_ (int_to_bv16 x))))
          (forall ((y_ (BitVec Size16)) ((= y_ (int_to_bv16 y))))
            (forall ((res_ (BitVec Size16)) ((= res_ (bvadd x_ y_))))
              ((= (bv16_to_int res_) 3)))))))
  )
)
-/
import LeanFixpoint

-- No kvars — ground bitvector arithmetic
def bitv8Prop : Prop :=
  -- 8-bit addition: 1 + 2 = 3
  (∀ x_ : BitVec 8, x_ = BitVec.ofNat 8 1 →
    ∀ y_ : BitVec 8, y_ = BitVec.ofNat 8 2 →
      ∀ res_ : BitVec 8, res_ = x_ + y_ →
        res_.toNat = 3)
  -- 16-bit addition: 1 + 2 = 3
  ∧ (∀ x_ : BitVec 16, x_ = BitVec.ofNat 16 1 →
      ∀ y_ : BitVec 16, y_ = BitVec.ofNat 16 2 →
        ∀ res_ : BitVec 16, res_ = x_ + y_ →
          res_.toNat = 3)

theorem bitv8Proof : bitv8Prop := by
  solve_fixpoint
