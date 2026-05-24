import Lean
import LeanFixpoint.Fusion.Types
import LeanFixpoint.Monad

open Lean Meta

/-- Discharge each `∃` at the head of `goal` by supplying a fresh
    metavariable as the witness.

    For a goal `?goal : ∃ κ : T, P κ`, builds the proof term
        `Exists.intro T (fun κ => P κ) ?κ ?proof`
    and assigns `?goal` to it, where:
      • `?κ : T` is a fresh `syntheticOpaque` mvar — the witness slot
        that fusion will later fill via `?κ.assign`.
      • `?proof : P ?κ` is a fresh mvar — the new proof obligation.

    Recurses on `?proof` while its type is another `∃`. Returns:
      • the map of κ-mvars (`MVarId` ↦ KVars) for fusion's detection,
      • the κ-binder names in source order,
      • the residual proof goal — body of the innermost ∃, with each
        existentially-bound variable replaced by its mvar. -/

partial def peelExistentialsAndIntro (goal : MVarId) :
    MetaM (Std.HashMap MVarId KVar × List KVar × MVarId) :=
  go goal {} []
where
  go (goal : MVarId) (kvars : Std.HashMap MVarId KVar) (kvarsRev : List KVar) :
      MetaM (Std.HashMap MVarId KVar × List KVar × MVarId) := do
    let goalType ← goal.getType >>= whnf
    -- goal is an existential: ∃ κ : α, P(κ)
    if goalType.isAppOfArity ``Exists 2 then
      let α     := goalType.getArg! 0 -- type α
      let pred  := goalType.getArg! 1 -- type P(κ)
      match pred with
      | .lam name tyBind body _ =>  -- λ κ : α, P(κ)
        -- Fresh κ-mvar at type α; synthethicOpaque so only we can assign it
        -- using `syntheticOpaque` stops the lean4 elaborator
        -- to do any form of automatic unification.
        let κMVar ← mkFreshExprMVar (some α)
                    (kind := .syntheticOpaque) (userName := name)
        -- new proof obligation: predicate body with
        -- κ ↦ ?κ
        -- P(κ) goes to P(?κ)
        let newType := body.instantiate1 κMVar
        -- We create new meta-variable for proof of ?κ MVar
        let proofMVar ← mkFreshExprMVar (some newType)
        -- Use the original Exists's universe
        let lvls := goalType.getAppFn.constLevels!
        let proof := mkApp4 (mkConst ``Exists.intro lvls) α pred κMVar proofMVar
        -- assign the proof (it is sort of like a place holder)
        goal.assign proof
        let (_, pTypes) ← collectArrowTypes tyBind
        let canonParams := (List.range pTypes.length).map fun i => Name.mkStr1 s!"z{i}"
        let kvar : KVar := {
          name
          params     := canonParams
          paramTypes := pTypes
          mvarId     := κMVar.mvarId!
        }
        go proofMVar.mvarId!
            (kvars.insert κMVar.mvarId! kvar)
            (kvar :: kvarsRev)
      | _ =>
        return (kvars, kvarsRev.reverse, goal)
    else
      return (kvars, kvarsRev.reverse, goal)
  collectArrowTypes (ty : Expr) : MetaM (Nat × List Expr) := do
    let ty ← whnf ty
    if ty.isForall then
      let domTy := ty.bindingDomain!
      let (n, rest) ← collectArrowTypes ty.bindingBody!
      return (1 + n, domTy :: rest)
    else return (0, [])
