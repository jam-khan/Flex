import Lean

open Lean Meta

initialize qualifAttr : TagAttribute ←
  registerTagAttribute `qualif "marks a definition as a refinement type qualifier for predicate abstraction."

-- Get all defs tagged as `@[qualif]`
def getQualifiers : MetaM (Array Expr) := do
  let names := qualifAttr.ext.getState (← getEnv)
  names.toArray.mapM fun n => do
    mkConstWithLevelParams n

-- Instantiate a qualifier by β-reduction
def Expr.instQualifier (q : Expr) (args : Array Expr) : MetaM Expr :=
  whnf (mkAppN q args)
