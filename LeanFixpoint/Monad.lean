import Lean
import Std
import LeanFixpoint.Core.Types

open Lean List Meta

/-!
  ## κ-Variable Context

  `KContext` tracks which `FVarId`s are κ-variables during `Expr` traversal.
  `KM` is a reader monad over `MetaM` carrying this context.
-/
structure KContext where
  kvars : Std.HashMap FVarId KVar

abbrev KM := ReaderT KContext MetaM

def KM.isKVar (id : FVarId) : KM Bool := do
  return (← read).kvars.contains id

def KM.getKVar? (id : FVarId) : KM (Option KVar) := do
  return (← read).kvars.get? id

def KM.getKVarList : KM (List KVar) := do
  return (← read).kvars.values

-- checks if expr is κ application
-- returning κ and args
def KM.isKApp (e : Expr) : KM (Option (KVar × Array Expr)) := do
  let fn := e.getAppFn
  if fn.isFVar then
    if let some κ ← KM.getKVar? fn.fvarId! then
      return some (κ, e.getAppArgs)
  return none

-- Collect all κ-variables referenced in an Expr
-- Strategy: check each known κ's fvarId against the expression
def KM.exprKVars (e : Expr) : KM (List KVar) := do
  let kvars ← KM.getKVarList
  return kvars.filter fun κ => e.containsFVar κ.fvarId
