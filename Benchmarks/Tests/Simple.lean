import LeanFixpoint

-- ∀ x : Int, 0 ≤ x → ∀ ν : Int, ν = x - 1 → 0 ≤ ν + 1
def simpleVC1 : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒ ∀ ν : int . ν == x - 1 ⇒ 0 ≤ ν + 1 }

#solve_constraint simpleVC1

-- ∀ x : Int, 0 ≤ x → ∀ ν : Int, ν = x + 1 → 0 ≤ ν
def simpleVC2 : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒ ∀ ν : int . ν == x + 1 ⇒ 0 ≤ ν }

#solve_constraint simpleVC2
