import LeanFixpoint
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

-- No κ-variables — pure VC about bit masking
-- This is a complex bitvector constraint: index & (size - 1) < size
-- when size is a power of 2 (size & (size - 1) == 0)
-- Expr passthrough: BitVec 32 is a native Lean type

-- NOTE: This VC is hard — it requires reasoning about bitvector
-- masking properties. The old system couldn't even EXPRESS this.
-- With Expr passthrough, at least we can state it.

def bitv_vc : Prop :=
  ∀ one_ : BitVec 32, one_ = BitVec.ofInt 32 1 →
  ∀ zero_ : BitVec 32, zero_ = BitVec.ofInt 32 0 →
  ∀ size : Int, 1 ≤ size →
  ∀ index : Int, 0 ≤ index →
  ∀ size_ : BitVec 32, size_ = BitVec.ofInt 32 size ∧ zero_ = size_ &&& (size_ - one_) →
  ∀ index_ : BitVec 32, index_ = BitVec.ofInt 32 index →
  ∀ mask_ : BitVec 32, mask_ = size_ - one_ →
  ∀ res_ : BitVec 32, res_ = index_ &&& mask_ →
  ∀ res : Int, res = res_.toInt →
    res < size

theorem bitv_proof : bitv_vc := by
  unfold bitv_vc
  intro one_ hone_ zero_ hzero_ size hsize index hindex size_ hsize_ index_ hindex_ mask_ hmask_ res_ hres_ res hres
  by_cases h : size % 2^32 = 0
  · grind
  · -- h : size % 2^32 ≠ 0
    subst hone_ hzero_ hindex_ hmask_ hres_ hres
    obtain ⟨hsize_eq, hpow⟩ := hsize_
    subst hsize_eq
    -- Goal: (BitVec.ofInt 32 index &&& (BitVec.ofInt 32 size - BitVec.ofInt 32 1)).toInt < size
    -- size_.toNat ≠ 0 because size % 2^32 ≠ 0
    have hsize_ne : (BitVec.ofInt 32 size).toNat ≠ 0 := by
      rw [BitVec.toNat_ofInt]; omega
    -- (size_ - 1).toNat = size_.toNat - 1 (no wrap since size_.toNat ≥ 1)
    have hsub : (BitVec.ofInt 32 size - BitVec.ofInt 32 1).toNat =
                (BitVec.ofInt 32 size).toNat - 1 := by
      rw [show BitVec.ofInt 32 1 = 1#32 from by decide,
          BitVec.toNat_sub, BitVec.toNat_one (by grind)]
      have := (BitVec.ofInt 32 size).isLt; omega
    -- res_.toNat ≤ mask_.toNat (and-with-mask ≤ mask)
    have hle : (BitVec.ofInt 32 index &&& (BitVec.ofInt 32 size - BitVec.ofInt 32 1)).toNat ≤
               (BitVec.ofInt 32 size - BitVec.ofInt 32 1).toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_right
    -- res_.toNat < size_.toNat
    have hlt : (BitVec.ofInt 32 index &&& (BitVec.ofInt 32 size - BitVec.ofInt 32 1)).toNat <
               (BitVec.ofInt 32 size).toNat := by omega
    -- size_.toNat ≤ size (since size ≥ size % 2^32 = size_.toNat)
    have hnat_le : ((BitVec.ofInt 32 size).toNat : Int) ≤ size := by
      rw [BitVec.toNat_ofInt]
      have : 0 ≤ size % (2 : Int) ^ 32 := Int.emod_nonneg _ (by grind)
      omega
    -- Split on sign of res_
    let r := (BitVec.ofInt 32 index &&& (BitVec.ofInt 32 size - BitVec.ofInt 32 1))
    rcases Nat.lt_or_ge (2 * r.toNat) (2 ^ 32) with hpos | hneg
    · -- r.toInt = r.toNat (non-negative signed value)
      have := BitVec.toInt_eq_toNat_of_lt hpos
      grind
    · -- r.toInt < 0
      have hbound := r.isLt
      have : r.toInt = (r.toNat : Int) - 2 ^ 32 := by simp [BitVec.toInt]; omega
      grind
