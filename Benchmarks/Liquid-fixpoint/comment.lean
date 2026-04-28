import LeanFixpoint
/-
  Demo: prove comment_vc by hoisting cut kvars to the front, then refining
  with metavariables for them. Cut kvars become outer mvars; the inner ∃'s
  for acyclic kvars + body becomes the residual goal.
-/

@[qualif] def q_le (a b : Int) : Prop := a ≤ b

-- Original: ∃ k1 k2 k3 k0 k5 k4, body  (acyclic-first)
def comment_vc : Prop :=
  ∃ k1 : Int → Int → Prop,
  ∃ k2 : Int → Int → Int → Prop,
  ∃ k3 : Int → Int → Int → Prop,
  ∃ k0 : Int → Int → Int → Prop,
  ∃ k5 : Int → Int → Int → Prop,
  ∃ k4 : Int → Int → Int → Prop,
    ∀ a0 : Int, ∀ a1 : Int, ∀ a2 : Bool,
      a0 < a1 →
        (a2 = false →
            k0 a1 a0 a1
          ∧ k1 a0 a1
          ∧ k2 a0 a0 a1
          ∧ (∀ a3 : Int, k0 a3 a0 a1 → k3 a3 a0 a1)
          ∧ (∀ a4 : Int, k0 a4 a0 a1 → k4 a4 a0 a1)
          ∧ (∀ a5 : Int, k4 a5 a0 a1 → k0 a5 a0 a1))
      ∧ (a2 = true →
            k5 a0 a0 a1
          ∧ k1 a0 a1
          ∧ (∀ a6 : Int, k5 a6 a0 a1 → k2 a6 a0 a1)
          ∧ k3 a1 a0 a1
          ∧ (∀ a7 : Int, k5 a7 a0 a1 → k4 a7 a0 a1)
          ∧ (∀ a8 : Int, k4 a8 a0 a1 → k5 a8 a0 a1))
      ∧ (k1 a0 a1 →
          ∀ a9 : Int, k4 a9 a0 a1 →
              (∀ a10 : Int, a10 = a9 + 1 → k4 a10 a0 a1)
            ∧ (∀ a11 : Int, k4 a11 a0 a1 →
                ∀ a12 : Int, k2 a12 a0 a1 →
                  ∀ a13 : Int, k3 a13 a0 a1 →
                    0 ≤ a11 - a0))

-- Reordered: ∃ k0 k4 k5 k1 k2 k3, body  (cut-first)
def comment_vc_reordered : Prop :=
  ∃ k0 : Int → Int → Int → Prop,
  ∃ k4 : Int → Int → Int → Prop,
  ∃ k5 : Int → Int → Int → Prop,
  ∃ k1 : Int → Int → Prop,
  ∃ k2 : Int → Int → Int → Prop,
  ∃ k3 : Int → Int → Int → Prop,
    ∀ a0 : Int, ∀ a1 : Int, ∀ a2 : Bool,
      a0 < a1 →
        (a2 = false →
            k0 a1 a0 a1
          ∧ k1 a0 a1
          ∧ k2 a0 a0 a1
          ∧ (∀ a3 : Int, k0 a3 a0 a1 → k3 a3 a0 a1)
          ∧ (∀ a4 : Int, k0 a4 a0 a1 → k4 a4 a0 a1)
          ∧ (∀ a5 : Int, k4 a5 a0 a1 → k0 a5 a0 a1))
      ∧ (a2 = true →
            k5 a0 a0 a1
          ∧ k1 a0 a1
          ∧ (∀ a6 : Int, k5 a6 a0 a1 → k2 a6 a0 a1)
          ∧ k3 a1 a0 a1
          ∧ (∀ a7 : Int, k5 a7 a0 a1 → k4 a7 a0 a1)
          ∧ (∀ a8 : Int, k4 a8 a0 a1 → k5 a8 a0 a1))
      ∧ (k1 a0 a1 →
          ∀ a9 : Int, k4 a9 a0 a1 →
              (∀ a10 : Int, a10 = a9 + 1 → k4 a10 a0 a1)
            ∧ (∀ a11 : Int, k4 a11 a0 a1 →
                ∀ a12 : Int, k2 a12 a0 a1 →
                  ∀ a13 : Int, k3 a13 a0 a1 →
                    0 ≤ a11 - a0))

-- Equivalence proof: just destructure and reconstruct in the new order.
theorem comment_vc_iff : comment_vc ↔ comment_vc_reordered := by
  unfold comment_vc comment_vc_reordered
  -- solve_fixpoint
  constructor
  · rintro ⟨k1, k2, k3, k0, k5, k4, h⟩
    exact ⟨k0, k4, k5, k1, k2, k3, h⟩
  · rintro ⟨k0, k4, k5, k1, k2, k3, h⟩
    exact ⟨k1, k2, k3, k0, k5, k4, h⟩

theorem baz :
    ∃ k1 : Int -> Prop,
    ∃ k2 : Int -> Prop,
    ∀x,
      (k1 x -> k2 x)
     ∧ (k2 x -> x > 0) := by
  apply Exists.imp (p := fun k1 => ∀x, k1 x -> x > 0)
  · intro k1 x
    exists (fun x => k1 x)
    grind
  · exists (fun x => x > 0)
    intros
    assumption
  