/-
(constraint
  (and
    (forall ((one_ (BitVec Size32)) ((= one_ (int_to_bv32 1))))
      (forall ((zero_ (BitVec Size32)) ((= zero_ (int_to_bv32 0))))
        (forall ((size Int) ((<= 1 size)))
          (forall ((index Int) ((<= 0 index)))
            (forall ((size_ (BitVec Size32)) (and
                                              ((= size_ (int_to_bv32 size)))
                                              ((= zero_ ((bvand size_) ((bvsub size_) one_))))))
              (forall ((index_ (BitVec Size32)) ((= index_ (int_to_bv32 index))))
                (forall ((mask_ (BitVec Size32)) ((= mask_ ((bvsub size_) one_))))
                  (forall ((res_ (BitVec Size32)) ((= res_ ((bvand index_) mask_))))
                    (forall ((res Int) ((= res (bv32_to_int res_))))
                      ((< res size)))))))))))))
-/
import LeanFixpoint

-- No kvars — power-of-two masking: index & (size-1) < size when size is a power of 2
-- size & (size - 1) = 0 encodes the power-of-two constraint
def bitvProp : Prop :=
  ∀ size : BitVec 32, ∀ index : BitVec 32,
    (size &&& (size - 1)) = 0 →
    size ≠ 0 →
    (index &&& (size - 1)).toNat < size.toNat

-- closers (grind/aesop/omega) can't handle this BV theorem yet — needs bv_omega or decide
theorem bitvProof : bitvProp := by
  sorry
