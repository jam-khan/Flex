import Lean
import LeanFixpoint.Core.Types

open Lean

-- Replace a free variable (by Name) with another in a Pred
def Pred.substVar (target : Var) (replacement : Var) : Pred → Pred
  | .expr e =>
    let t := Expr.fvar (FVarId.mk target)
    let r := Expr.fvar (FVarId.mk replacement)
    .expr (e.replaceFVar t r)
  | .kapp k args =>
    let t := Expr.fvar (FVarId.mk target)
    let r := Expr.fvar (FVarId.mk replacement)
    .kapp k (args.map fun a => a.replaceFVar t r)
  | .conj p₁ p₂ =>
    .conj (p₁.substVar target replacement) (p₂.substVar target replacement)

def Pred.applyKVarSol (κ : KVar) (sol : Pred) (args : List Expr) : Pred :=
  let argNames := args.map fun a => a.fvarId!.name
  let pairs := κ.params.zip argNames
  pairs.foldl (fun acc (param, arg) => acc.substVar param arg) sol

def Pred.substKVar (κ : KVar) (sol : Pred) (p : Pred) : Pred :=
  match p with
  | .expr e      => .expr e
  | .kapp k args =>
    if k == κ then Pred.applyKVarSol κ sol args
    else .kapp k args
  | .conj p₁ p₂ =>
    .conj (Pred.substKVar κ sol p₁) (Pred.substKVar κ sol p₂)
