import Lean
import LeanFixpoint.Core

open Lean Meta

-- Build witness lambda: fun (z0 : T0) (z1 : T1) ... => sol
-- Replaces fake canonical fvars (FVarId.mk `z0) with real fvars before abstracting
def solToWitnessExpr (sol : Expr) (params : List Name) (paramTypes : List Expr) : MetaM Expr := do
  let rec go (sol : Expr) (fvars : Array Expr) : List (Name × Expr) → MetaM Expr
    | [] => mkLambdaFVars fvars sol
    | (n, ty) :: rest =>
      withLocalDeclD n ty fun fvar => do
        let sol' := sol.replaceFVar (.fvar (FVarId.mk n)) fvar
        go sol' (fvars.push fvar) rest
  go sol #[] (params.zip paramTypes)
