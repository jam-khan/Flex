import Lean

import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Subst
import LeanFixpoint.Core.Macros
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Fusion
import LeanFixpoint.Solve.Qualifier

open Lean Meta Elab Term Tactic

-- Build Pred (conjunction of qualifiers) from a list of RExpr
def conjoinQualifiers (qs : List RExpr) : Pred :=
  match qs.map Pred.rexpr with
  | []      => Pred.tru
  | [p]     => p
  | p :: ps => ps.foldl Pred.conj p

-- Extract actual args from κ-application in head
def getHeadArgs : Pred → KVar → List Var
  | .kapp k args, κ => if k == κ then args else []
  | .conj p₁ p₂, κ => getHeadArgs p₁ κ ++ getHeadArgs p₂ κ
  | _, _ => []

/-- All ordered k-tuples drawn from `xs` (with no repeats) -/
partial def kPerms [BEq α] (k : Nat) (xs : List α) : List (List α) :=
  if k == 0 then [[]]
  else xs.flatMap fun x =>
    (kPerms (k-1) (xs.erase x)).map (x :: ·)

-- Replace κ's formal params with actual args in a qualifier
def instantiateQualWithArgs (κ : KVar) (q : RExpr) (args : List Var) : RExpr :=
  let pairs := κ.params.zip args
  pairs.foldl (fun acc (param, arg) => RExpr.subst param (.var arg) acc) q

/-- Replace the leaf predicate in a flat constraint (head position) -/
def replaceLeafPred : Constraint → Pred → Constraint
  | .pred _, p => .pred p
  | .imp x b hyp c, p => .imp x b hyp (replaceLeafPred c p)
  | .conj _ _, _ => .pred .tru  -- shouldn't happen on flat constraints
