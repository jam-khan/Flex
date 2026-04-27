import LeanFixpoint
/-

-- SOLVED USING GRIND
-- HOWEVER, pure grind and aesop don't work
-- solve-fixpoint enables intros and constructors that made
-- it feasible for grind and/or aesop to close the goal


(fixpoint "--eliminate=horn")

(constraint
  (and
    (forall ((x Str) ((= x "cat")))
      (forall ((y Str) ((= y "dog")))
        (and
          ((= x "cat"))
          ((= y "dog")))))))
-/

def scrape03Prop : Prop :=
  ∀ x : String, x = "cat" → ∀ y : String, y = "dog" → x = "cat" ∧ y = "dog"

theorem scrape03Proof : scrape03Prop := by
  solve_fixpoint
