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
          -- Substitute κ's canonical param fvars (`z0`, `z1`, …) with the call's
          -- args, ALL AT ONCE. A sequential `foldl` of `replaceFVar` is unsound:
          -- (1) it cascades when an arg mentions a later param's name, and
          -- (2) it corrupts a loose-`bvar` arg (e.g. a κ-app under an existential
          -- `∃ a5, ?κ a5 …` arising from a fused/inlined clause), mapping the
          -- param to the wrong value. `replaceFVars` does one simultaneous pass.
          let n := min κ.params.length args.size
          let paramFvars := ((κ.params.take n).map
            (fun p => Expr.fvar (FVarId.mk p))).toArray
          some (sol.replaceFVars paramFvars (args.extract 0 n))
      -- return none
      else none
