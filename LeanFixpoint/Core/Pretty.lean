import Lean
import LeanFixpoint.Core.Types

open Lean

private def parenIf (p : Bool) (s : String) : String :=
  if p then "(" ++ s ++ ")" else s

instance : ToString BaseTy where
  toString | .int => "Int" | .bool => "Bool"

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

def ppConstraint (indent : Nat := 0) : Constraint → MetaM String
  | .pred p => do return s!"{← Meta.ppExpr p}"
  | .conj c1 c2 => do
      let pad := "".pushn ' ' indent
      return s!"{← ppConstraint indent c1}\n{pad}∧ {← ppConstraint indent c2}"
  | .imp x ty p c => do
      let pad := "".pushn ' ' (indent + 2)
      return s!"∀ {x} : {← Meta.ppExpr ty}.\n{pad}{← Meta.ppExpr p}\n{pad}⇒ {← ppConstraint (indent + 2) c}"
