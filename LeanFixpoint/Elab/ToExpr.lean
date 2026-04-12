import Lean
import LeanFixpoint.Core.Types

open Lean Meta

def Constraint.toExpr : Constraint → MetaM Expr
  | .pred e => return e
  | .conj c₁ c₂ => do
      mkAppM ``And #[← c₁.toExpr, ← c₂.toExpr]
  | .imp x ty hyp c => do
      withLocalDeclD x ty fun fvar => do
        let body ← c.toExpr
        let imp ← mkArrow hyp body
        mkForallFVars #[fvar] imp

def solToWitnessExpr (sol : Expr) (params : List Name) : MetaM Expr := do
  let rec go (fvars : Array Expr) : List Name → MetaM Expr
    | [] => mkLambdaFVars fvars sol
    | n :: rest =>
      withLocalDeclD n (mkConst ``Int) fun fvar => do
        go (fvars.push fvar) rest
  go #[] params
