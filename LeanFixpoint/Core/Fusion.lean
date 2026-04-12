import LeanFixpoint.Core.Types
import LeanFixpoint.Core.Pretty
import LeanFixpoint.Core.Macros
import LeanFixpoint.Monad

open Lean

-- Extract `kvars` from constraint `c`
def Constraint.kvars : Constraint → KM (List KVar)
  | .pred e          => KM.exprKVars e
  | .conj c₁ c₂      => return (← c₁.kvars) ++ (← c₂.kvars)
  | .imp _ _ p _ c   => return (← KM.exprKVars p) ++ (← c.kvars)

/-
  WARNING: Constraint.head and .body shall
  only be called on Flattened Horn Constraints
-/
-- the innermost predicate (the goal)
def Constraint.head : Constraint → Expr
  | .pred e          => e
  | .imp _ _ _ _ c   => c.head
  -- shouldn't happen on flat constraints
  | .conj _ _        => (mkConst ``True)

-- all hypothesis predicates (which are in terms of Lean4 `Expr`)
def Constraint.body : Constraint → List Expr
  | .pred _          => []
  | .imp _ _ p _ c   => p :: c.body
  | .conj _ _        => []

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
  | .pred e            => if e.isConstOf ``True then [] else [⟨.pred e⟩]
  | .conj c₁ c₂        => c₁.flat ++ c₂.flat
  | .imp x ty p fv c   => c.flat.map (fun ⟨c'⟩ => ⟨.imp x ty p fv c'⟩)

/-
  Dependencies `deps(c)` over constraints
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

  Based on `Fig. 9` of the paper `Local Refinement Typing`
-/
def Constraint.scope (κ : KVar) : Constraint → KM Constraint
  | .conj c₁ c₂ => do
    let inC₁ := (← c₁.kvars).contains κ
    let inC₂ := (← c₂.kvars).contains κ
    if inC₁ && !inC₂ then c₁.scope κ
    else if !inC₁ && inC₂ then c₂.scope κ
    else return .conj c₁ c₂
  | .imp x ty p fv c' => do
    if !(← KM.exprKVars p).contains κ
    then return .imp x ty p fv (← c'.scope κ)
    else return .imp x ty p fv c'
  | c => return c

-- Expr-level simplification of And/Or/Exists with True/False propagation
partial def simplifyExpr (e : Expr) : Expr :=
  if e.isAppOfArity ``And 2 then
    let args := e.getAppArgs
    let l := simplifyExpr args[0]!
    let r := simplifyExpr args[1]!
    if l.isConstOf ``False || r.isConstOf ``False then mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  else if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    let l := simplifyExpr args[0]!
    let r := simplifyExpr args[1]!
    if l.isConstOf ``True || r.isConstOf ``True then mkConst ``True
    else if l.isConstOf ``False then r
    else if r.isConstOf ``False then l
    else mkApp2 (mkConst ``Or) l r
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
  `sol1 : (K × C) → Expr`

  sol1(κ, c) is strongest solution (Section 5.2).
  Uses Expr.abstract to properly close fvars into bvars
  when building ∃ binders.
-/
def Constraint.sol1 (κ : KVar) (c : Constraint) (simplify := false) : Expr :=
  let raw := sol1Aux c
  if simplify then simplifyExpr raw else raw
  where
    sol1Aux : Constraint → Expr
      | .conj c₁ c₂ =>
          mkApp2 (mkConst ``Or) (sol1Aux c₁) (sol1Aux c₂)
      | .imp _x ty p fv c =>
        let inner := mkApp2 (mkConst ``And) p (sol1Aux c)
        let abstrBody := inner.abstract #[fv]
        if abstrBody.hasLooseBVars then
          -- fvar was used in body → real ∀, need ∃
          let lam := Expr.lam _x ty abstrBody .default
          mkApp2 (mkConst ``Exists [levelOne]) ty lam
        else
          -- fvar wasn't used → bare arrow, just conjoin
          inner
      | .pred e =>
          if e.getAppFn.isFVar && e.getAppFn.fvarId! == κ.fvarId then
            let args := e.getAppArgs.toList
            let eqs := (κ.params.zip (args.zip κ.paramTypes)).map fun (pi, (ai, ty)) =>
              mkApp3 (mkConst ``Eq [levelOne]) ty
                (.fvar (FVarId.mk pi)) ai
            match eqs with
            | []      => mkConst ``True
            | [e]     => e
            | e :: es => es.foldl (mkApp2 (mkConst ``And)) e
          else mkConst ``False

-- Replace κ(arg₁, ..., argₙ) with sol[z₀ := arg₁, ..., zₙ := argₙ]
-- sol has free canonical params (z0, z1, ...) which get replaced by actual args
-- Replace κ(arg₁, ..., argₙ) with sol[z₀ := arg₁, ..., zₙ := argₙ]
def substKVarInExpr (κ : KVar) (sol : Expr) (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.getAppFn.isFVar && sub.getAppFn.fvarId! == κ.fvarId then
      let args := sub.getAppArgs
      let result := (κ.params.zip args.toList).foldl
        (fun acc (param, arg) => acc.replaceFVar (.fvar (FVarId.mk param)) arg) sol
      some result
    else none

/-
  `elim* : (σ × C) → C` from Fig. 11
-/
def Constraint.elimStar (κ : KVar) (sol : Expr) : Constraint → Constraint
  | .conj c₁ c₂       => .conj (c₁.elimStar κ sol) (c₂.elimStar κ sol)
  | .imp x ty p fv c   => .imp x ty (substKVarInExpr κ sol p) fv (c.elimStar κ sol)
  | .pred e            =>
      if e.getAppFn.isFVar && e.getAppFn.fvarId! == κ.fvarId
      then .pred (mkConst ``True)
      else .pred (substKVarInExpr κ sol e)

def stripScope (κ : KVar) : Constraint → KM Constraint
  | .imp x ty p fv c => do
      if !(← KM.exprKVars p).contains κ then stripScope κ c
      else return .imp x ty p fv c
  | c => return c

def collectScopeVars (κ : KVar) : Constraint → KM (List Var)
  | .imp x _ p _ c => do
      if !(← KM.exprKVars p).contains κ then return x :: (← collectScopeVars κ c)
      else return []
  | _ => return []

-- Collect the fvars of scope variables (needed to replace them in solutions)
def collectScopeFVars (κ : KVar) : Constraint → KM (List Expr)
  | .imp _ _ p fv c => do
      if !(← KM.exprKVars p).contains κ then return fv :: (← collectScopeFVars κ c)
      else return []
  | _ => return []

def Constraint.elim1 (κ : KVar) (c : Constraint) : KM Constraint := do
  let scoped' ← c.scope κ
  let c'      ← stripScope κ scoped'
  let sol     := c'.sol1 κ
  return c.elimStar κ sol

def Constraint.elim (kvars : List KVar) (c : Constraint) : KM Constraint := do
  let mut acc := c
  for κ in kvars do
    acc ← acc.elim1 κ
  return acc

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
