import Flex

@[qualif] def q_gez (v : Int) : Prop := 0 ≤ v

def ex : Prop :=
  ∃ κseed : Int → Int → Prop,
  ∃ κinv  : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κseed ν x)                  -- seed:  κseed ⊒ {ν = x}
    ∧ (∀ v : Int, κseed v x → κinv v x)               -- entry: κseed ⊑ κinv
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)              -- loop:  κinv self-cycle
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)                   -- check: κinv ⊑ {0 ≤ ν}

example : ex := by
  unfold ex
  reorderKs
  case κinv  => exact fun ν _ => 0 ≤ ν      -- κinv  := λ ν _. 0 ≤ ν
  case κseed => exact fun ν x => ν = x      -- κseed := λ ν x. ν = x
  grind                                     -- discharge the now-instantiated body

example : ex := by
  unfold ex
  solK1 κseed
  solve_fixpoint

example : ex := by
  unfold ex
  fusion
  fixpoint

example : ex := by
  unfold ex
  solve_fixpoint
