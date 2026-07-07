import Flex
import Mathlib.Data.Set.Basic

structure MyData (α : Type) where
  mkdata :: field1 : α

def issue701 : Prop :=
  ∀ x : MyData (Set Int), 0 ∈ x.field1 → 0 ∈ x.field1

theorem issue701_proof : issue701 := by
  solve_fixpoint
  