import Flex
import Mathlib.Data.Set.Basic

-- (datatype (MyData 1) ((mkdata ((field1 @(0))))))
-- A single-field record parameterised by α; `@(0)` = first type parameter.
structure MyData (α : Type) where
  mkdata :: field1 : α

-- (constraint
--   (forall ((x (MyData (Set_Set int))) ((Set_mem 0 (field1 x))))
--     ((Set_mem 0 (field1 x)))))
def issue701 : Prop :=
  ∀ x : MyData (Set Int), 0 ∈ x.field1 → 0 ∈ x.field1

theorem issue701_proof : issue701 := by
  solve_fixpoint
