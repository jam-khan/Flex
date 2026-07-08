import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqKeyMatches
import LeanProofs.User.Fun.SvecLen
import Flex

namespace F

@[qualif]
abbrev BMIGe0 (i : Int) : Prop := i ≥ 0

@[qualif]
abbrev BMILSub (v : OVec (ASeq Int Int)) (i1 i2 : Int) : Prop :=
  v.length = i1 - i2

@[qualif]
abbrev BMIAllNil (v : OVec (ASeq Int Int)) : Prop :=
  ∀ b ∈ v, b = .nil

@[qualif]
def SameKeys (l1 l2 : ASeq Int Int) (k : Int) : Prop :=
  alist_aseq_contains_key l1 k ↔ alist_aseq_contains_key l2 k

@[qualif]
def AllKeysMatch (l1 l2 : ASeq Int Int) (k : Int) : Prop :=
  ∀ x, alist_aseq_key_matches l1 k x ↔ alist_aseq_key_matches l2 k x

-- @[qualif]
-- def SameLength (v1 v2 : OVec (ASeq Int Int)) : Prop :=
--   svec_len v1 = svec_len v2

-- @[qualif]
-- def EmptyUpTo (v1 : OVec (ASeq Int Int)) (i : Int): Prop :=
--   ∀ j : Nat, j < i → v1[j]! = .nil

-- @[qualif]
-- def EqualFrom (v1 v2 : OVec (ASeq Int Int)) (i : Int) : Prop :=
--   ∀ j : Nat, j ≥ i → v1[j]! = v2[j]!
end F
