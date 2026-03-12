-- Qualifier.lean
import LeanFixpoint.Syntax
import LeanFixpoint.Subst
import LeanFixpoint.Macros

structure Qualifier where
  /-- Predicate template with placeholder variable `v` -/
  pred : RExpr
deriving Repr, BEq

/-- Insantiate qualifier: replace `v` with the `k`'s param name -/
def Qualifier.instantiate (q : Qualifier) (paramName : Var) : RExpr :=
  RExpr.subst `v (.var paramName) q.pred

section Examples

def sumQualifiers : List Qualifier := [
  { pred := r{ 0 ≤ v } },   -- non-negative
  { pred := r{ v ≤ 0 } },   -- non-positive
]

-- Show raw AST of qualifiers
#eval sumQualifiers.map (fun q => repr q.pred)
-- [RExpr.cmp (CmpOp.le) (RExpr.int 0) (RExpr.var `v),
--  RExpr.cmp (CmpOp.le) (RExpr.var `v) (RExpr.int 0)]

-- Show pretty-printed qualifiers
#eval sumQualifiers.map (fun q => toString q.pred)
-- ["0 <= v", "v <= 0"]

-- Instantiate with κ's param name `z`
#eval sumQualifiers.map (fun q => toString (q.instantiate `z))
-- ["0 <= z", "z <= 0"]

-- Instantiate with different param names
#eval sumQualifiers.map (fun q => toString (q.instantiate `k))
-- ["0 <= k", "k <= 0"]

#eval sumQualifiers.map (fun q => toString (q.instantiate `ν))
-- ["0 <= ν", "ν <= 0"]

-- More interesting qualifiers
def arithQualifiers : List Qualifier := [
  { pred := r{ 0 ≤ v } },       -- non-negative
  { pred := r{ 0 ≤ v + 1 } },   -- almost non-negative
  { pred := r{ v == 0 } },      -- zero
]

#eval arithQualifiers.map (fun q => toString q.pred)
-- ["0 <= v", "0 <= v + 1", "v == 0"]

#eval arithQualifiers.map (fun q => toString (q.instantiate `z))
-- ["0 <= z", "0 <= z + 1", "z == 0"]

-- Show that instantiate only replaces `v`, not other variables
def relationalQual : Qualifier := { pred := r{ x ≤ v } }

#eval toString relationalQual.pred
-- "x <= v"

#eval toString (relationalQual.instantiate `z)
-- "x <= z"    (only `v` replaced, `x` stays)

end Examples
