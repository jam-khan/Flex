import Lean
import LeanFixpoint.Solve.Qualifier

open Lean Meta

-- Walk outer `∀`-chain of a type,
-- collect the domain types.
-- Stop at the first non-forall.
private partial def qualifParamTypes (ty : Expr) : List Expr :=
  if ty.isForall then ty.bindingDomain! ::qualifParamTypes ty.bindingBody!
  else []

-- All ordered κ-tuples
private partial def kPerms {α} [BEq α] (k : Nat) (xs : List α) : List (List α) :=
  if k == 0 then [[]]
  else xs.flatMap fun x =>
    (kPerms (k - 1) (xs.erase x)).map (x :: ·)
