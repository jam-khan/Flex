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

private def ppPred : Pred → String
  | .expr r        => toString r
  | .kapp k args    =>
      let ps := ", ".intercalate (args.map toString)
      s!"{k.name}[{ps}]"
  | .conj p q       => s!"({ppPred p} ∧ {ppPred q})"
  
instance : ToString Pred where toString := ppPred

-- Indentation-aware printing for constraints
private def ppConstraint (indent : Nat := 0) : Constraint → String
  | .pred p        => ppPred p
  | .conj c1 c2    =>
      let pad := String.ofList (List.replicate indent ' ')
      s!"{ppConstraint indent c1}\n{pad}∧ {ppConstraint indent c2}"
  | .imp x b p c   =>
      let pad  := String.ofList (List.replicate (indent + 2) ' ')
      s!"∀ {x} : {b}.\n{pad}{ppPred p}\n{pad}⇒ {ppConstraint (indent + 2) c}"

instance : ToString Constraint where toString c := ppConstraint 0 c
