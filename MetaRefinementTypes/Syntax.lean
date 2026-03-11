import Lean

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
  -- `p₁ ∨ p₂`
  | disj  : Pred → Pred → Pred
  -- `∃x:b. p`
  | exist : Var → BaseTy → Pred → Pred
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

-- elaboration

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
  Pretty printing
-/

instance : ToString ArithOp where
  toString | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

instance : ToString CmpOp where
  toString | .eq => "==" | .ne => "!=" | .lt => "<"
            | .le => "<=" | .gt => ">"  | .ge => ">="

instance : ToString BoolOp where
  toString | .and => "∧" | .or => "∨" | .imp => "⇒"

instance : ToString BaseTy where
  toString | .int => "Int" | .bool => "Bool"

private def parenIf (p : Bool) (s : String) : String :=
  if p then "(" ++ s ++ ")" else s

private def arithPrec : ArithOp → Nat
  | .mul | .div => 70 | .add | .sub => 60

private def cmpPrec   : CmpOp → Nat  := fun _ => 50
private def bopPrec   : BoolOp → Nat
  | .and => 40 | .or => 30 | .imp => 20

mutual
  private def ppRExprPrec (prec : Nat) : RExpr → String
    | .var v       => toString v
    | .int i       => toString i
    | .bool b      => if b then "true" else "false"
    | .not r       =>
        parenIf (prec > 80) s!"¬{ppRExprPrec 81 r}"
    | .app f args  =>
        let argStr := ", ".intercalate (args.map (ppRExprPrec 0))
        s!"{f}({argStr})"
    | .arith op l r =>
        let p := arithPrec op
        parenIf (prec > p) s!"{ppRExprPrec p l} {op} {ppRExprPrec (p+1) r}"
    | .cmp op l r   =>
        let p := cmpPrec op
        parenIf (prec > p) s!"{ppRExprPrec (p+1) l} {op} {ppRExprPrec (p+1) r}"
    | .bop op l r   =>
        let p := bopPrec op
        parenIf (prec > p) s!"{ppRExprPrec (p+1) l} {op} {ppRExprPrec p r}"
end

instance : ToString RExpr where toString r := ppRExprPrec 0 r

private def ppRType : RType → String
  | .tvar α           => toString α
  | .base x b r       => s!"\{{x} : {b} | {r}}"
  | .fn x dom cod     =>
      let domStr := match dom with
        | .fn _ _ _ => s!"({ppRType dom})"   -- add parens for nested arrows
        | _         => ppRType dom
      s!"({x} : {domStr}) → {ppRType cod}"
  | .forallTy α t     => s!"∀ {α}. {ppRType t}"

instance : ToString RType where toString := ppRType

private def ppUType : UType → String
  | .tvar α          => toString α
  | .base b          => toString b
  | .fn x dom cod    =>
      let domStr := match dom with
        | .fn _ _ _ => s!"({ppUType dom})"
        | _         => ppUType dom
      s!"({x} : {domStr}) → {ppUType cod}"
  | .forallTy α t    => s!"∀ {α}. {ppUType t}"

instance : ToString UType where toString := ppUType

instance : ToString KVar where
  toString k :=
    if k.params.isEmpty then toString k.name
    else
      let ps := ", ".intercalate (k.params.map toString)
      s!"{k.name}({ps})"

private def ppPred : Pred → String
  | .tru            => "⊤"
  | .fls            => "⊥"
  | .rexpr r        => toString r
  | .kapp k args    =>
      let ps := ", ".intercalate (args.map toString)
      s!"{k.name}[{ps}]"
  | .conj p q       => s!"({ppPred p} ∧ {ppPred q})"
  | .disj p q       => s!"({ppPred p} ∨ {ppPred q})"
  | .exist x b p    => s!"∃ {x} : {b}. {ppPred p}"

instance : ToString Pred where toString := ppPred

private def ppConstraint (indent : Nat := 0) : Constraint → String
  | .pred p        => ppPred p
  | .conj c1 c2    =>
      let pad := String.ofList (List.replicate indent ' ')
      s!"{ppConstraint indent c1}\n{pad}∧ {ppConstraint indent c2}"
  | .imp x b p c   =>
      let pad  := String.ofList (List.replicate (indent + 2) ' ')
      s!"∀ {x} : {b}.\n{pad}{ppPred p}\n{pad}⇒ {ppConstraint (indent + 2) c}"

instance : ToString Constraint where toString c := ppConstraint 0 c


section Examples

def exRType : RType :=
  .base `ν .int (.cmp .gt (.var `ν) (.int 0))

def exFnType : RType :=
  .fn `x
    (.base `ν .int (.cmp .gt (.var `ν) (.int 0)))
    (.base `ν .int (.cmp .ge (.var `ν) (.var `x)))

-- A Horn constraint: ∀ x : Int. κ(x) ∧ x > 0 ⇒ κ(x+1)
def exConstraint : Constraint :=
  .imp `x .int
    (.conj (.kapp ⟨`κ, [`x]⟩ [`x]) (.rexpr (.cmp .gt (.var `x) (.int 0))))
    (.pred (.kapp ⟨`κ, [`x]⟩ [`x]))

#eval toString exRType
-- {ν : Int | ν > 0}

#eval toString exFnType
-- (x : {ν : Int | ν > 0}) → {ν : Int | ν >= x}

#eval toString exConstraint
-- ∀ x : Int.
--   (κ[x] ∧ x > 0)
--   ⇒ κ[x]

#eval IO.println (toString exRType)
#eval IO.println (toString exFnType)
#eval IO.println (toString exConstraint)

end Examples
