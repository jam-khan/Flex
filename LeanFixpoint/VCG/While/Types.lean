import Lean

open Lean

abbrev CVar := String

abbrev State := CVar → Int

def State.update (s : State) (x : CVar) (v : Int) : State :=
  fun y => if x == y then v else s y

notation s "[" x " ↦ " v "]" => State.update s x v

inductive AExpr where
  | var : CVar → AExpr
  | lit : Int → AExpr
  | add : AExpr → AExpr → AExpr
  | sub : AExpr → AExpr → AExpr
  | mul : AExpr → AExpr → AExpr
deriving Repr, Inhabited, BEq

inductive BExpr where
  | tt  : BExpr
  | ff  : BExpr
  | eq  : AExpr → AExpr → BExpr
  | le  : AExpr → AExpr → BExpr
  | lt  : AExpr → AExpr → BExpr
  | not : BExpr → BExpr
  | and : BExpr → BExpr → BExpr
  | or  : BExpr → BExpr → BExpr
deriving Repr, Inhabited, BEq

inductive Cmd where
  | skip   : Cmd
  | assign : CVar → AExpr → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : BExpr → Cmd → Cmd → Cmd
  | cwhile : BExpr → Cmd → Cmd
deriving Repr, Inhabited
