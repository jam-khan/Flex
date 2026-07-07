import Lean
import Flex.PA.Qualifier

open Lean Meta

-- Nav outer `∀`-chain of a type,
-- collect the domain types.
-- Stop at the first non-forall.
private partial def qualifParamTypes (ty : Expr) : List Expr :=
  if ty.isForall then ty.bindingDomain! ::qualifParamTypes ty.bindingBody!
  else []

/--
  `kPerms k xs` returns every ordered `k`-tuple drawn from `xs` without
  repeating elements (i.e. all k-permutations of `xs`).

  Used to enumerate every way a qualifier's parameter slots can be bound
  to a κ-variable's arguments. Output size = `|xs| · (|xs|-1) · … · (|xs|-k+1)`.

  kPerms 2 [a, b, c]
    = [[a,b], [a,c], [b,a], [b,c], [c,a], [c,b]]   -- 3 × 2 = 6 tuples
 -/
private partial def kPerms {α} [BEq α] (k : Nat) (xs : List α) : List (List α) :=
  if k == 0 then [[]]
  else xs.flatMap fun x =>
    (kPerms (k - 1) (xs.erase x)).map (x :: ·)

/-- Given a qualifier lambda `q` and the κ's parameter types, return every
    slot assignment of qualifier-params to κ-slots that type-checks.

    Output: `Array (q, slotIndices)` pairs where `slotIndices[i]` says which
    κ-slot binds qualifier param `i`. β-application at actual κ-args is
    deferred to weakening time (see `specializeClauseForHead`).

    Example: for `q_le : Int → Int → Prop` and a 4-arg κ of all `Int`s,
    this returns 12 pairs `(q_le, [i, j])` for every ordered pair `i ≠ j ∈ 0..3`. -/
def instantiateQualifier
    (q : Expr) (kvarParamTypes : List Expr)
    : MetaM (Array (Expr × List Nat)) := do
  let qTy        ← inferType q
  let paramTypes := qualifParamTypes qTy
  let n          := paramTypes.length
  let kvarArity  := kvarParamTypes.length
  let perms      := kPerms n (List.range kvarArity)
  let mut out    : Array (Expr × List Nat) := #[]
  for perm in perms do
    let mut ok := true
    for (pt, idx) in paramTypes.zip perm do
      let kpt := kvarParamTypes[idx]!
      unless (← isDefEq pt kpt) do ok := false; break
    if ok then
      out := out.push (q, perm)
  return out
