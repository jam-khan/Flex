import LeanFixpoint

inductive Adt0 | mk0 | mk1 deriving Nonempty
noncomputable opaque f_get_mode : BitVec 32 → Int → Adt0

@[qualif] def q_eq_mode (a : Int) (m : BitVec 32) : Prop :=
  f_get_mode m a = Adt0.mk0

-- Add k0 fusion (acyclic) feeding into k4 alongside the k4↔k5 cycle
def reproVC : Prop :=
  ∃ k0 : Int → BitVec 32 → Int → Prop,
  ∃ k4 : Int → Int → Int → Int → BitVec 32 → Int → Prop,
  ∃ k5 : Int → BitVec 32 → Int → Int → Int → Int → Prop,
    ∀ reftgen : BitVec 32, ∀ a0 : Int,
      (∀ a1 : Int,
          f_get_mode reftgen a1 = Adt0.mk0 → k0 a1 reftgen a0)
    ∧ (∀ a4 : Int, k0 a4 reftgen a0 →
          ∀ a5 a6 : Int, k4 a4 a5 a6 a0 reftgen a0)
    ∧ (∀ a7 : Int,
          (∀ a11 a12 a13 : Int, k4 a11 a7 a12 a13 reftgen a0 →
              ∀ a14 a15 : Int, k5 a11 reftgen a0 a7 a14 a15)
        ∧ (∀ a24 a25 a26 : Int, k5 a24 reftgen a0 a7 a25 a26 →
              ∀ a27 a28 a29 : Int, k4 a24 a27 a28 a29 reftgen a0)
        ∧ (∀ a17 a18 a19 : Int,
              k5 a17 reftgen a0 a7 a18 a19 →
                f_get_mode reftgen a17 = Adt0.mk0))

set_option maxHeartbeats 6400000 in
theorem reproVC_proof : reproVC := by
  solve_fixpoint
