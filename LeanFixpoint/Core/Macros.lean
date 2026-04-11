import Lean
import LeanFixpoint.Core.Types

open Lean

declare_syntax_cat constr

syntax term : constr
syntax:30 constr:31 " ∧ " constr:30 : constr
syntax "∀" ident ":" ident "," term "⇒" constr : constr
syntax "[" constr "]" : constr

syntax "c{" constr "}" : term

-- Limitation, only supports types like Int, Bool for macros
-- and can't write compound types yet.
macro_rules
  | `(c{ $l ∧ $r })
      =>  `(Constraint.conj c{$l} c{$r})
  | `(c{ ∀ $x:ident : $ty:ident , $hyp:term ⇒ $body:constr })
      =>  `(Constraint.imp $(quote x.getId) (Lean.mkConst $(quote ty.getId)) $hyp c{$body})
  | `(c{ $p:term })
      =>  `(Constraint.pred $p)
  | `(c{ [ $e:constr ] }) => `(c{$e})

-- Helpers
open Lean in
def mkFVar (n : Name) : Expr := .fvar (FVarId.mk n)
def mkTrue : Expr := mkConst ``True

-- Examples using c{...} macro
section Examples

def ex1 : Constraint :=
  c{ ∀ x : Int, mkTrue ⇒
      [∀ y : Int, mkTrue ⇒ mkTrue] }

end Examples
