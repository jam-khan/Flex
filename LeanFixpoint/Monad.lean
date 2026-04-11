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
