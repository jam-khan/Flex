import Lean

open Lean

abbrev Var    := Name
abbrev TyVar  := Name

inductive BaseTy where
  | int   : BaseTy
  | bool  : BaseTy
deriving BEq, Repr, Inhabited, DecidableEq
-- note: decidableEq allows us to get proof for equality

-- Unrefined type
inductive UType where
  | tvar      : TyVar → UType
  | base      : BaseTy → UType
  | fn        : Var → UType → UType → UType
  | forallTy  : TyVar → UType → UType
deriving BEq, Repr, Inhabited, DecidableEq

-- refinement expressions, later we can use Lean4 expressions
-- for simplicity, now we perform a deep embedding of
-- refinement expressions which will get elaborated into
-- Lean4 Expr
-- Why not use Lean4 Expr directly?
-- For now, it adds complexity and pattern matching on Lean4
-- Expr is much more cumbersome.
inductive ArithOp where
  | add | sub | mul
deriving BEq, Repr, DecidableEq

inductive CmpOp where
  | eq | ne | lt | le | gt | ge
deriving BEq, Repr, DecidableEq

inductive BoolOp where
  | and | or | imp
deriving BEq, Repr, DecidableEq

inductive RExpr where
  | var   : Var → RExpr
  | int   : Int → RExpr
  | bool  : Bool → RExpr
  | arith : ArithOp → RExpr → RExpr → RExpr
  | cmp   : CmpOp → RExpr → RExpr → RExpr
  | bop   : BoolOp → RExpr → RExpr → RExpr
  | not   : RExpr → RExpr
  | app   : Var → List RExpr → RExpr
deriving BEq, Repr, Inhabited

def RExpr.tt : RExpr := .bool true
def RExpr.ff : RExpr := .bool false
def RExpr.mkEq (l r : RExpr) : RExpr := .cmp .eq l r

-- Refined type
inductive RType where
  | tvar     : TyVar → RType
  | base     : Var → BaseTy → RExpr → RType
  | fn       : Var → RType → RType → RType
  | forallTy : TyVar → RType → RType
deriving BEq, Repr, Inhabited

def RType.erase : RType → UType
  | .tvar α        => .tvar α
  | .base _ b _    => .base b
  | .fn x t1 t2    => .fn x t1.erase t2.erase
  | .forallTy α t  => .forallTy α t.erase

structure KVar where
  name    : Name
  params  : List Name
deriving BEq, Hashable, Repr, Inhabited

instance : Hashable KVar where
  hash k := hash k.name

inductive Pred where
  | tru   : Pred
  | fls   : Pred
  | rexpr : RExpr → Pred
  | kapp  : KVar → List Var → Pred
  | conj  : Pred → Pred → Pred
deriving Repr, Inhabited

inductive Constraint where
  | pred : Pred → Constraint
  | conj : Constraint → Constraint → Constraint
  | imp  : Var → BaseTy → Pred → Constraint → Constraint
deriving Repr, Inhabited

abbrev TyEnv := List (Var × RType)

structure Assumption where
  var  : Var
  ty   : BaseTy
  pred : Pred
deriving Repr

abbrev Assumptions := List Assumption

def Assignment := List (String × (List Var × RExpr))

structure FlatHornClause where
  hyps : List (Var × BaseTy × Pred)
  goal : Pred
deriving Repr

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
