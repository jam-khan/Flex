import LeanFixpoint
/-
(constraint
  (and
    (forall ((x_ (BitVec Size4)) ((= x_ (lit "#b1000" (BitVec Size4)))))
      (forall ((y_ (BitVec Size4)) ((= y_ (app (_ rotate_right 7) x_))))
        (forall ((z_ (BitVec Size4)) ((= z_ (lit "#b0001" (BitVec Size4)))))
            ((= y_ z_))
        )
      )
    )
    (forall ((x (BitVec Size32)) (true))
      (forall ((y (BitVec Size32)) ((= x y)))
    	  ((= (app (_ sign_extend 64) x) (app (_ sign_extend 64) y)))
      )
    )
  )
)
-/

-- No κ-variables — pure VCs on bitvectors
-- Expr passthrough: BitVec 4 and BitVec 32 are native Lean types

def bitvec_ii_vc : Prop :=
    -- rotate_right 8 (#b1000) by 7 = #b0001
    (∀ x_ : BitVec 4, x_ = 0b1000#4 →
      ∀ y_ : BitVec 4, y_ = x_.rotateRight 7 →
        ∀ z_ : BitVec 4, z_ = 0b0001#4 →
          y_ = z_)
  ∧ -- sign_extend preserves equality
    (∀ x : BitVec 32,
      ∀ y : BitVec 32, x = y →
        x.signExtend 64 = y.signExtend 64)

theorem bitvec_ii_proof : bitvec_ii_vc := by
  solve_fusion
