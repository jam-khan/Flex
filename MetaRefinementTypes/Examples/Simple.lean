import MetaRefinementTypes.Constraint
import MetaRefinementTypes.Elab
import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Macros

-- ∀ x : Int, 0 ≤ x → ∀ ν : Int, ν = x - 1 → 0 ≤ ν + 1
def simpleVC2 : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒ ∀ ν : int . ν == x - 1 ⇒ 0 ≤ ν + 1 }

-- ∀ x : Int, 0 ≤ x → ∀ ν : Int, ν = x + 1 → 0 ≤ ν
def simpleVC3 : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒ ∀ ν : int . ν == x + 1 ⇒ 0 ≤ ν }

#check_vc simpleVC2
#check_vc simpleVC3
