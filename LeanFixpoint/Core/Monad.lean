import Lean
import Std
import LeanFixpoint.Core.KVar

open Lean List Meta

/-!
  ## κ-Variable Context

  `KContext` tracks which `MVarId`s are κ-variables during `Expr` traversal.
  `KM` is a reader monad over `MetaM` carrying this context.
-/
structure KContext where
  kvars : Std.HashMap MVarId KVar

abbrev KM := ReaderT KContext MetaM

def KM.isKVar (id : MVarId) : KM Bool := do
  return (← read).kvars.contains id

def KM.getKVar? (id : MVarId) : KM (Option KVar) := do
  return (← read).kvars.get? id

def KM.getKVarList : KM (List KVar) := do
  return (← read).kvars.values

-- checks if expr is κ application
-- returning κ and args
def KM.isKApp (e : Expr) : KM (Option (KVar × Array Expr)) := do
  -- let e ← instantiateMVars e
  let fn := e.getAppFn
  if fn.isMVar then
    if let some κ ← KM.getKVar? fn.mvarId! then
      return some (κ, e.getAppArgs)
  return none

-- Equivalent to e.constainsFVar, but custom addition
-- checks if an Expr contains reference to MVar or not
-- it instantiatesMVar e first to ensure possible mvars
-- are resolved.
def Lean.Expr.containsMVar (e : Expr) (mvarId : MVarId) : Bool :=
  e.hasMVar && (e.find? fun sub => sub.isMVar && sub.mvarId! == mvarId).isSome

-- Collect all κ-variables referenced in an Expr
-- Strategy: check each known κ's mvarId against the expression
def KM.exprKVars (e : Expr) : KM (List KVar) := do
  let kvars ← KM.getKVarList
  -- let e ← instantiateMVars e
  return kvars.filter fun κ => e.containsMVar κ.mvarId

-- walk outer `∀`-binders of a flat clause to reach the leaf head.
-- if leaf is κ-application, return that κ; otherwise, return `none`.
partial def findHeadKVar (fc : Expr) : KM (Option KVar) := do
  let fc ← whnf fc
  if fc.isForall then
    withLocalDeclD fc.bindingName! fc.bindingDomain! fun fvar =>
      findHeadKVar (fc.bindingBody!.instantiate1 fvar)
  else
    match ← KM.isKApp fc with
    | some (κ, _) => return some κ
    | none        => return none
