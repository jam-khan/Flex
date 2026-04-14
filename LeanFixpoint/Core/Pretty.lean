import Lean
import LeanFixpoint.Core.Types

open Lean

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
  | .imp x ty p _fv c => do
      let pad := "".pushn ' ' (indent + 2)
      return s!"∀ {x} : {← Meta.ppExpr ty}.\n{pad}{← Meta.ppExpr p}\n{pad}⇒ {← ppConstraint (indent + 2) c}"
