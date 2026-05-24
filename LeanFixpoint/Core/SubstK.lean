import Lean
import LeanFixpoint.Core.KVar

open Lean Meta

/-
  β-substitution for expression `e`

  Arguments:
  - κ   : refinement variable
  - sol : solution for κ
  - e   : expression in which κ occurs

  `κ` is replaced with `sol` inside `e`.
-/
def substKVarInExpr (κ : KVar) (sol : Expr) (e : Expr) : Expr :=
  e.replace
    fun x =>
      if  -- check if x is a function application `f a₁ .. aₙ`, then check if `f` is a meta-variable
            x.getAppFn.isMVar
          -- given `f` is a meta-variable, get meta-var id and compare to that of `κ`
          -- if it is same, then proceed
        &&  x.getAppFn.mvarId! == κ.mvarId
        then
          -- if x is `f a₁ .. aₙ`, then args gets `#[a₁, .., aₙ]`
          let args := x.getAppArgs
          -- Creates a list of (param, arg) pairs
          -- then, performs a left fold operation passing `sol`
          -- so, replaces `param` with `arg` in `sol`, and passes result as `acc`
          -- and repeats this through each (`param`, `arg`) pair in the list.
          let result := (κ.params.zip args.toList).foldl
            (fun acc (param, arg) => acc.replaceFVar (.fvar (FVarId.mk param)) arg) sol
          -- return result
          some result
      -- return none
      else none
