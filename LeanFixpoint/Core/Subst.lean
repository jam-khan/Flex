import Lean
import LeanFixpoint.Core.Types

open Lean

-- Replace a stable name-keyed fvar in an Expr with a replacement Expr
def replaceInExpr (target : Name) (replacement : Expr) (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isFVar && sub.fvarId!.name == target then some replacement else none

partial def Pred.substVar (target : Var) (replacement : Var) : Pred → Pred
  | .tru          => .tru
  | .fls          => .fls
  | .rexpr r        => .rexpr r
  | .eqVars pi ai   => .eqVars (if pi == target then replacement else pi)
                                (if ai == target then replacement else ai)
  | .kapp k args    => .kapp k (args.map fun a =>
      replaceInExpr target (mkFVar { name := replacement }) a)
  | .conj p₁ p₂   => .conj (Pred.substVar target replacement p₁) (Pred.substVar target replacement p₂)
  | .disj p₁ p₂   => .disj (Pred.substVar target replacement p₁) (Pred.substVar target replacement p₂)
  | .exist x b p  =>
        if x == target then .exist x b p                -- shadowed, stop
        else if x == replacement then
          -- Alpha-rename to avoid capture
          let x' := Name.mkStr1 s!"{x}_α"
          let p' := Pred.substVar x x' p
          .exist x' b (Pred.substVar target replacement p')
        else .exist x b (Pred.substVar target replacement p)
  | .eqExpr v e   => .eqExpr (if v == target then replacement else v) e

-- Substitute a param name with an Expr throughout a Pred
partial def Pred.substExpr (target : Name) (replacement : Expr) : Pred → Pred
  | .tru          => .tru
  | .fls          => .fls
  | .rexpr r      => .rexpr (replaceInExpr target replacement r)
  | .eqVars pi ai =>
      let pi' := if pi == target then replacement else mkFVar { name := pi }
      let ai' := if ai == target then replacement else mkFVar { name := ai }
      -- Try to stay as eqVars if both are simple fvars
      if pi'.isFVar && ai'.isFVar then
        .eqVars pi'.fvarId!.name ai'.fvarId!.name
      else if pi'.isFVar then
        .eqExpr pi'.fvarId!.name ai'
      else if ai'.isFVar then
        .eqExpr ai'.fvarId!.name pi'
      else
        -- Both compound — build raw Eq expr
        .rexpr (mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Int) pi' ai')
  | .eqExpr v e   =>
      let e' := replaceInExpr target replacement e
      if v == target then
        if replacement.isFVar then
          .eqExpr replacement.fvarId!.name e'
        else
          -- v replaced by compound expr — build raw Eq
          .rexpr (mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Int) replacement e')
      else .eqExpr v e'
  | .kapp k args  =>
      .kapp k (args.map fun a => replaceInExpr target replacement a)
  | .conj p₁ p₂  => .conj (Pred.substExpr target replacement p₁) (Pred.substExpr target replacement p₂)
  | .disj p₁ p₂  => .disj (Pred.substExpr target replacement p₁) (Pred.substExpr target replacement p₂)
  | .exist x b p  =>
      if x == target then .exist x b p  -- shadowed
      else .exist x b (Pred.substExpr target replacement p)

-- Apply a kvar solution by substituting each param with the corresponding arg Expr
def Pred.applyKVarSol (κ : KVar) (sol : Pred) (args : List Expr) : Pred :=
  let pairs := κ.params.zip args
  pairs.foldl (fun acc (param, argExpr) => acc.substExpr param argExpr) sol

def Pred.substKVar (κ : KVar) (sol : Pred) : Pred → Pred
  | .tru            => .tru
  | .fls            => .fls
  | .rexpr r        => .rexpr r
  | .eqVars pi ai   => .eqVars pi ai
  | .kapp k args    =>
    if k == κ then Pred.applyKVarSol κ sol args
    else .kapp k args
  | .conj p₁ p₂  => .conj (Pred.substKVar κ sol p₁) (Pred.substKVar κ sol p₂)
  | .disj p₁ p₂  => .disj (Pred.substKVar κ sol p₁) (Pred.substKVar κ sol p₂)
  | .exist x b p  => .exist x b (Pred.substKVar κ sol p)
  | .eqExpr v e   => .eqExpr v e
