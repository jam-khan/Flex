import Lean
import Init.Data.List

open Lean List

abbrev Var    := Name
abbrev TyVar  := Name

/-
  BaseTy is a basic types, that is,
  either `int` or `bool`.
-/
inductive BaseTy where
  | int   : BaseTy
  | bool  : BaseTy
-- note: decidableEq allows us to get proof for equality
deriving BEq, Repr, Inhabited, DecidableEq

/-
  UType is an unrefined type.

  Essentially, it does `NOT` contains a type
  of form `{x : b | r}` where `b` is a base type,
  and `r` is a refinement.
-/
inductive UType where
  -- type variable `α`
  | tvar      : TyVar → UType
  -- b (`int` or `bool`)
  | base      : BaseTy → UType
  -- `x : τ → τ`, where `τ` is a `UType`
  | fn        : Var → UType → UType → UType
  -- `∀α. τ`, where `α` is a type variable
  | forallTy  : TyVar → UType → UType
deriving BEq, Repr, Inhabited, DecidableEq

/-
  **Definition of Refinements**
  Refinements `r` := ...

  Here, we have two choices:
  1) Use `Lean.Syntax` as a refinement `r`.
  2) Use `Lean.Expr` as a refinement `r`.
  2) Define custom deep embedding for `r` and then,
  elaborate into `Lean.Expr`.

  We choose option 3.
  Why?

    - It is cumbersome to pattern match on `Lean.Syntax` and
    `Lean.Expr`. Former is verbose with multiple source-level
    sugared constructs and latter is too abstract.

    - Using custom embedding for now, keeps initial
    prototype simple and it will still get elaborated into
    `Lean.Expr`, except we do need to define the `elaboration`.

-/

-- + | - | * | /
inductive ArithOp where
  | add | sub | mul | div
deriving BEq, Repr, DecidableEq

-- == | != | < | <= | > | >=
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
deriving BEq, Repr, DecidableEq

-- ∧ | ∨ | →
inductive BoolOp where
  | and | or | imp
deriving BEq, Repr, DecidableEq

-- Refinement expressions
inductive RExpr where
  -- κ
  | var   : Var → RExpr
  -- i
  | int   : Int → RExpr
  -- bool (`true` or `false`)
  | bool  : Bool → RExpr
  -- r₁ `ArithOp` r₂
  | arith : ArithOp → RExpr → RExpr → RExpr
  -- r₁ `CmpOp` r₂
  | cmp   : CmpOp → RExpr → RExpr → RExpr
  -- r₁ `BoolOp` r₂
  | bop   : BoolOp → RExpr → RExpr → RExpr
  -- `!r`
  | not   : RExpr → RExpr
  -- `κ(r₁, …, rₙ)`
  | app   : Var → List RExpr → RExpr
deriving BEq, Repr, Inhabited

/-
  `RType` is a refined type.

  It is similar to an unrefined type, except
  it can contain a base type `b` with a refinement
  `r` of form `{x : b | r}`.
-/
inductive RType where -- Refined type `t`
  -- `α`
  | tvar     : TyVar → RType
  -- `{x : b | r}`
  | base     : Var → BaseTy → RExpr → RType
  -- `x : t → t`, note here fun input and out
  -- types can be refined type `t` unlike `Utype`
  | fn       : Var → RType → RType → RType
  -- `∀α. t`
  | forallTy : TyVar → RType → RType
deriving BEq, Repr, Inhabited

/-
  **Horn Constraints**

  Representing syntax for constraints from `Fig. 5`.
-/

-- κ(x₁, ..., xₙ)
structure KVar where
  name    : Name      -- κ
  params  : List Name -- x₁, ..., xₙ
deriving BEq, Hashable, Repr, Inhabited

instance : Hashable KVar where
  hash k := hash k.name

-- Predicates `p`
inductive Pred where
  -- `true`
  | tru   : Pred
  -- `false`
  | fls   : Pred
  -- refinement `r`
  | rexpr : RExpr → Pred
  -- `κ(y₁, ..., yₙ)`
  | kapp  : KVar → List Var → Pred
  -- `p₁ ∧ p₂`
  | conj  : Pred → Pred → Pred
deriving Repr, Inhabited

-- Constraints c
inductive Constraint where
  -- `p`
  | pred : Pred → Constraint
  -- `c₁ ∧ c₂`
  | conj : Constraint → Constraint → Constraint
  -- `∀ x : b. p ⇒ c`
  | imp  : Var → BaseTy → Pred → Constraint → Constraint
deriving Repr, Inhabited

-- Some sugared utils for `r`
def RExpr.tt : RExpr := .bool true
def RExpr.ff : RExpr := .bool false
def RExpr.mkEq (l r : RExpr) : RExpr := .cmp .eq l r

/-
  Wrapper for flattened constraint.

  It helps to identify using type system
  whether a constraint has been flattened or
  not, and hence, avoiding wrong calls for
  .head and .body on Constraint
-/
structure FlatConstraint where
  val : Constraint
deriving Repr, Inhabited

-- Γ ::= `map x → t`
abbrev TyEnv := List (Var × RType)

-- Below models `σ`
abbrev Assignment := List (KVar × (List Var × Pred))

-- `{x: b | p}`
structure Assumption where
  var  : Var
  ty   : BaseTy
  pred : Pred
deriving Repr

-- CHECK THIS CAREFULLY
abbrev Assumptions := List Assumption

/-
  Procedure `Shape` from `Section 4.4`
  in `Local Refinement Typing`.

  Erases refinements from a refined type `t`
  returning unrefined type `τ`.
-/
def RType.erase : RType → UType
  | .tvar α        => .tvar α
  -- {x : b | r} ⤳ b
  | .base _ b _    => .base b
  | .fn x t1 t2    => .fn x t1.erase t2.erase
  | .forallTy α t  => .forallTy α t.erase

-- Extract `kvars` from predicate `p`
def Pred.kvars : Pred → List KVar
  | .tru        => []
  | .fls        => []
  | .rexpr _    => []
  | .kapp k _   => [k]
  | .conj p₁ p₂ => p₁.kvars ++ p₂.kvars

-- Extract `kvars` from constraint `c`
def Constraint.kvars : Constraint → List KVar
  | .pred p       => p.kvars
  | .conj c₁ c₂   => c₁.kvars ++ c₂.kvars
  | .imp _ _ p c  => p.kvars ++ c.kvars

/-
  WARNING: Constraint.head and .body shall
  only be called on Flattened Horn Constraints
-/
-- the innermost predicate (the goal)
def Constraint.head : Constraint → Pred
  | .pred p      => p
  | .imp _ _ _ c => c.head
  -- shouldn't happen on flat constraints
  | .conj _ _    => .tru

-- all hypothesis predicates
def Constraint.body : Constraint → List Pred
  | .pred _       => []
  | .imp _ _ p c  => p :: c.body
  | .conj _ _     => []

def FlatConstraint.head (fc: FlatConstraint) : Pred := fc.val.head
def FlatConstraint.body (fc: FlatConstraint) : List Pred := fc.val.body
def FlatConstraint.kvars (fc: FlatConstraint) : List KVar :=
  fc.val.kvars

/-
  `flat : Constraint → list FlatConstraint`

  It performs flattening on Horn Clauses
  based on `flat` in `Fig. 12.`

  Note: Order is left to right, c₁ => ⋯ => cₙ => p
-/
def Constraint.flat : Constraint → List FlatConstraint
  | .pred .tru    => []
  | .pred p       => [⟨.pred p⟩]
  | .conj c₁ c₂   => c₁.flat ++ c₂.flat
  | .imp x b p c  => c.flat.map (fun ⟨c'⟩ => ⟨.imp x b p c'⟩)

/-
  Dependencies `deps(c)` over constraints

  Deals with two cases:
  deps(c) ≅ {(κ, κ') | κ ∈ body(c), k' ∈ head(c)} -- flat constraint `c`
  deps(c) ≅ ⋃ deps(c'), where c' ∈ flat(c) -- NNF constraint `c`
-/
def FlatConstraint.deps (fc : FlatConstraint) : List (KVar × KVar) :=
  let bodyKs := (fc.body.map Pred.kvars).flatten
  let headKs := fc.head.kvars
  (bodyKs.map (fun kb => headKs.map (fun kh => (kb, kh)))).flatten

def Constraint.deps (c : Constraint) : List (KVar × KVar) :=
  (c.flat.map (fun c' => c'.deps)).flatten

-- Dependencies in `deps(σ)`
def Assignment.deps (σ : Assignment) : List (KVar × KVar) :=
  σ.flatMap fun (k', (_, body)) =>
    body.kvars.map fun k => (k, k')

-- `deps(K̂, c) = deps(c) \ (K × K̂ U K̂ × K)`, exclude pairs involving K̂
def Constraint.depsExcluding (c : Constraint) (khat : List KVar) : List (KVar × KVar) :=
  c.deps.filter fun (k1, k2) => !khat.contains k1 && !khat.contains k2

-- NOTE: Careful with this one, try to get a terminating function
partial def RExpr.subst (target : Var) (val : RExpr) : RExpr → RExpr
  | .var x        => if x == target then val else .var x
  | .int n        => .int n
  | .bool b       => .bool b
  | .arith op l r => .arith op (l.subst target val) (r.subst target val)
  | .cmp op l r   => .cmp op (l.subst target val) (r.subst target val)
  | .bop op l r   => .bop op (l.subst target val) (r.subst target val)
  | .not e        => .not (e.subst target val)
  | .app f args   => .app f (args.map fun a => a.subst target val)

def RExpr.substMany (params : List Var) (args : List Var) (body : RExpr) : RExpr :=
  (params.zip args).foldl (fun acc (p, a) => acc.subst p (.var a)) body

def nu : Var := String.toName "v"

def primInt (n : Int) : RType :=
  .base nu .int (RExpr.mkEq (.var nu) (.int n))

def primAssert : RType :=
  .fn (String.toName "x") (.base nu .bool (.var nu))
           (.base nu .bool RExpr.tt)
