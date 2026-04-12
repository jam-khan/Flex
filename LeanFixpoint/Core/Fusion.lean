import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Macros
import LeanFixpoint.Monad

open Lean

-- Extract `kvars` from constraint `c`
-- this is
def Constraint.kvars : Constraint → KM (List KVar)
  | .pred e       => KM.exprKVars e
  | .conj c₁ c₂   => return (← c₁.kvars) ++ (← c₂.kvars)
  | .imp _ _ p c  => return (← KM.exprKVars p) ++ (← c.kvars)

/-
  WARNING: Constraint.head and .body shall
  only be called on Flattened Horn Constraints
-/
-- the innermost predicate (the goal)
def Constraint.head : Constraint → Expr
  | .pred e      => e
  | .imp _ _ _ c => c.head
  -- shouldn't happen on flat constraints
  | .conj _ _    => (mkConst ``True)

-- all hypothesis predicates (which are in terms of Lean4 `Expr`)
def Constraint.body : Constraint → List Expr
  | .pred _       => []
  | .imp _ _ p c  => p :: c.body
  | .conj _ _     => []

def FlatConstraint.head (fc: FlatConstraint)  : Expr           := fc.val.head
def FlatConstraint.body (fc: FlatConstraint)  : List Expr      := fc.val.body
def FlatConstraint.kvars (fc: FlatConstraint) : KM (List KVar) := fc.val.kvars

/-
  `flat : Constraint → list FlatConstraint`

  It performs flattening on Horn Clauses
  based on `flat` in `Fig. 12.`

  Note: Order is left to right, c₁ => ⋯ => cₙ => p
-/
def Constraint.flat : Constraint → List FlatConstraint
  | .pred e =>
    if e.isConstOf ``True then [] else [⟨.pred e⟩]
  | .conj c₁ c₂     => c₁.flat ++ c₂.flat
  | .imp x b p c    => c.flat.map (fun ⟨c'⟩ => ⟨.imp x b p c'⟩)

/-
  Dependencies `deps(c)` over constraints

  Deals with two cases:
  deps(c) ≅ {(κ, κ') | κ ∈ body(c), k' ∈ head(c)} -- flat constraint `c`
  deps(c) ≅ ⋃ deps(c'), where c' ∈ flat(c) -- NNF constraint `c`
-/
def FlatConstraint.deps (fc : FlatConstraint) : KM (List (KVar × KVar)) := do
  let bodyKs := (← fc.body.mapM KM.exprKVars).flatten
  let headKs ← KM.exprKVars fc.head
  return (bodyKs.map (fun kb => headKs.map (fun kh => (kb, kh)))).flatten

def Constraint.deps (c : Constraint) : KM (List (KVar × KVar)) := do
  let deps ← c.flat.mapM (fun c' => c'.deps)
  return deps.flatten

-- Dependencies in `deps(σ)`
def Assignment.deps (σ : Assignment) : KM (List (KVar × KVar)) := do
  let mut result : List (KVar × KVar) := []
  for (k', (_, body)) in σ do
    let ks ← KM.exprKVars body
    result := result ++ ks.map fun k => (k, k')
  return result


-- `deps(K̂, c) = deps(c) \ (K × K̂ U K̂ × K)`, exclude pairs involving K̂
def Constraint.depsExcluding (c : Constraint) (khat : List KVar) : KM (List (KVar × KVar)) := do
  let deps ← c.deps
  return deps.filter fun (k1, k2) => !khat.contains k1 && !khat.contains k2


/-
  `scope : (K × C) → C`

  `scope` takes a `κ` variable and constraint `c`
  then, it returns a sub-constraint c of the form
  `∀(xᵢ:pᵢ) => c'` s.t.
    1) κ does not occur in any pᵢ
    2) all occurences of κ in c occur in c'

  Based on `Fig. 9` of the paper `Local Refinement Typing`
  and explained in `Section 5.1`.
-/
def Constraint.scope (κ : KVar) : Constraint → KM Constraint
  | .conj c₁ c₂ => do
    let inC₁ := (← c₁.kvars).contains κ
    let inC₂ := (← c₂.kvars).contains κ
    if inC₁ && !inC₂ then c₁.scope κ
    else if !inC₁ && inC₂ then c₂.scope κ
    else return .conj c₁ c₂
  | .imp x ty p c' => do
    if !(← KM.exprKVars p).contains κ
    then return .imp x ty p (← c'.scope κ)
    else return .imp x ty p c'
  | c => return c

-- Expr-level simplification of And/Or/Exists with True/False propagation
-- Needed by sol1 to eliminate dead branches (e.g. ∃ x. p ∧ False ≡ False)
partial def simplifyExpr (e : Expr) : Expr :=
  -- And l r
  if e.isAppOfArity ``And 2 then
    let args := e.getAppArgs
    let l := simplifyExpr args[0]!
    let r := simplifyExpr args[1]!
    if l.isConstOf ``False || r.isConstOf ``False then mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  -- Or l r
  else if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    let l := simplifyExpr args[0]!
    let r := simplifyExpr args[1]!
    if l.isConstOf ``True || r.isConstOf ``True then mkConst ``True
    else if l.isConstOf ``False then r
    else if r.isConstOf ``False then l
    else mkApp2 (mkConst ``Or) l r
  -- Exists ty (fun x => body)
  else if e.isAppOfArity ``Exists 2 then
    let args := e.getAppArgs
    let ty   := args[0]!
    let body := args[1]!
    match body with
    | .lam n t b bi =>
      let b' := simplifyExpr b
      if b'.isConstOf ``False then mkConst ``False
      else mkApp2 (mkConst ``Exists [levelOne]) ty (.lam n t b' bi)
    | _ => e
  else e

/-
  `sol1 : (K × C) → P`

  sol1(κ, c) is strongest solution
  procedure in `Section 5.2`.

  It returns a predicate that is
  guaranteed to satisfy all clauses
  where κ appears as the head.

  `Note`
    Rule `sol1(κ, ∀ x : b. p ⇒ c') ≡ ∃ x : b. p ∧ sol1(κ, c)`

    If we don't simplify,
      then we can get a case where
      `sol1` returns `∃ x : b. p ∧ false`
      where logically `p ∧ false ≡ false`
      so `p` might be left over with a `κ`

  Simplification is called if explicitly asked.
-/
def Constraint.sol1 (κ : KVar) (c : Constraint) (simplify := false) : Expr :=
  let raw := sol1Aux c
  if simplify then simplifyExpr raw else raw
  where
    sol1Aux : Constraint → Expr
      | .conj c₁ c₂  =>
          mkApp2 (mkConst ``Or) (sol1Aux c₁) (sol1Aux c₂)
      | .imp x ty p c =>
          mkApp2 (mkConst ``Exists [levelOne]) ty
            (mkLambda x .default ty (mkApp2 (mkConst ``And) p (sol1Aux c)))
      | .pred e       =>
          if e.getAppFn.isFVar && e.getAppFn.fvarId! == κ.fvarId then
            let args := e.getAppArgs.toList
            let eqs := (κ.params.zip args).map fun (pi, ai) =>
              mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Int)
                (.fvar (FVarId.mk pi)) ai
            match eqs with
            | []      => mkConst ``True
            | [e]     => e
            | e :: es => es.foldl (mkApp2 (mkConst ``And)) e
          else mkConst ``False


def substKVarInExpr (κ : KVar) (sol : Expr) (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.getAppFn.isFVar && sub.getAppFn.fvarId! == κ.fvarId then
      some (sol.beta sub.getAppArgs)
    else none

/-
  `elim* : (σ × C) → C` from Fig. 11

  Replaces all occurrences of κ in c:
  - body (hypothesis): κ(args) → σ(κ) applied to args
  - head (goal): κ(args) → true (eliminated)
-/
def Constraint.elimStar (κ : KVar) (sol : Expr) : Constraint → Constraint
  | .conj c₁ c₂  => .conj (c₁.elimStar κ sol) (c₂.elimStar κ sol)
  | .imp x ty p c => .imp x ty (substKVarInExpr κ sol p) (c.elimStar κ sol)
  | .pred e       =>
      if e.getAppFn.isFVar && e.getAppFn.fvarId! == κ.fvarId
      then .pred (mkConst ``True)
      else .pred (substKVarInExpr κ sol e)

/-
  `elim1 : (K × C) → C` from Fig. 11

  elim1(κ, c) = elimStar(κ, sol, c)
  where sol = sol1(κ, c') and scope(κ, c) = ∀(xᵢ:pᵢ) ⇒ c'
-/
def stripScope (κ : KVar) : Constraint → KM Constraint
  | .imp x ty p c => do
      if !(← KM.exprKVars p).contains κ then stripScope κ c
      else return .imp x ty p c
  | c => return c

/-- Collect the forall-bound variable names that `stripScope` would remove.
    These are the "scope variables" for κ — universally quantified variables
    whose hypotheses don't mention κ. -/
def collectScopeVars (κ : KVar) : Constraint → KM (List Var)
  | .imp x _ p c => do
      if !(← KM.exprKVars p).contains κ then return x :: (← collectScopeVars κ c)
      else return []
  | _ => return []

def Constraint.elim1 (κ : KVar) (c : Constraint) : KM Constraint := do
  let scoped' ← c.scope κ
  let c'      ← stripScope κ scoped'
  let sol     := c'.sol1 κ
  return c.elimStar κ sol

/-
  `elim : (List K × C) → C` from Fig. 12

  Iteratively eliminate each κ.
-/
def Constraint.elim (kvars : List KVar) (c : Constraint) : KM Constraint := do
  let mut acc := c
  for κ in kvars do
    acc ← acc.elim1 κ
  return acc


/-
  Cycle detection - `partitionKVars`
  and Eliminating Cyclic KVars
-/

/-- Check if κ appears in both head and body of any flat clause -/
def KVar.isCyclic (κ : KVar) (c : Constraint) : KM Bool := do
  let deps ← c.deps
  return deps.any fun (κ1, κ2) => κ1 == κ && κ2 == κ

/-- Split kvars into (acyclic, cyclic) -/
def Constraint.partitionKVars (c : Constraint) : KM (List KVar × List KVar) := do
  let allKs := (← c.kvars).eraseDups
  let cuts ← allKs.filterM (fun κ => κ.isCyclic c)
  let acyclic ← allKs.filterM (fun κ => return !(← κ.isCyclic c))
  return (acyclic, cuts)
