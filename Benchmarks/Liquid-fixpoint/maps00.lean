import Mathlib
import Flex

def maps00Prop : Prop :=
  ∀ m1 : Int → Int, m1 = (fun _ => 0) →
    (∀ v : Int, v = m1 100 → v = 0)
    ∧ (∀ m2 : Int → Int,
        m2 = Function.update (Function.update m1 10 1) 20 2 →
          (∀ v : Int, v = m2 10 → v = 1)
          ∧ (∀ v : Int, v = m2 20 → v = 2)
          ∧ (∀ v : Int, v = m2 30 → v = 0))

theorem maps00Proof : maps00Prop := by
  intro m1 hm1
  subst hm1
  refine ⟨by simp, fun m2 hm2 => ?_⟩
  subst hm2
  simp [Function.update_self, Function.update_of_ne]
