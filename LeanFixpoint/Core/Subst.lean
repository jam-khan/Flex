import Lean
import LeanFixpoint.Core.Types

open Lean

partial def RExpr.subst (target : Var) (val : RExpr) : RExpr → RExpr
  | .var x        => if x == target then val else .var x
  | .int n        => .int n
  | .bool b       => .bool b
  | .arith op l r => .arith op (RExpr.subst target val l) (RExpr.subst target val r)
  | .cmp op l r   => .cmp op (RExpr.subst target val l) (RExpr.subst target val r)
  | .bop op l r   => .bop op (RExpr.subst target val l) (RExpr.subst target val r)
  | .not e        => .not (RExpr.subst target val e)
  | .app f args   => .app f (args.map fun a => RExpr.subst target val a)

partial def Pred.substVar (target : Var) (replacement : Var) : Pred → Pred
  | .tru          => .tru
  | .fls          => .fls
  | .rexpr r      => .rexpr (RExpr.subst target (.var replacement) r)
  | .kapp k args  => .kapp k (args.map fun a => if a == target then replacement else a)
  | .conj p₁ p₂  => .conj (Pred.substVar target replacement p₁) (Pred.substVar target replacement p₂)
  | .disj p₁ p₂  => .disj (Pred.substVar target replacement p₁) (Pred.substVar target replacement p₂)
  | .exist x b p  =>
        if x == target then .exist x b p                -- shadowed, stop
        else if x == replacement then
          -- Alpha-rename to avoid capture
          let x' := Name.mkStr1 s!"{x}_α"
          let p' := Pred.substVar x x' p
          .exist x' b (Pred.substVar target replacement p')
        else .exist x b (Pred.substVar target replacement p)

def Pred.applyKVarSol (κ : KVar) (sol : Pred) (args : List Var) : Pred :=
  let pairs := κ.params.zip args
  pairs.foldl (fun acc (param, arg) => acc.substVar param arg) sol

def Pred.substKVar (κ : KVar) (sol : Pred) : Pred → Pred
  | .tru          => .tru
  | .fls          => .fls
  | .rexpr r      => .rexpr r
  | .kapp k args  =>
    if k == κ then Pred.applyKVarSol κ sol args
    else .kapp k args
  | .conj p₁ p₂  => .conj (Pred.substKVar κ sol p₁) (Pred.substKVar κ sol p₂)
  | .disj p₁ p₂  => .disj (Pred.substKVar κ sol p₁) (Pred.substKVar κ sol p₂)
  | .exist x b p  => .exist x b (Pred.substKVar κ sol p)

def RExpr.substMany (params : List Var) (args : List Var) (body : RExpr) : RExpr :=
  (params.zip args).foldl (fun acc (p, a) => acc.subst p (.var a)) body
