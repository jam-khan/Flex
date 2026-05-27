import Lean
import LeanFixpoint.Core

open Lean Meta Elab Tactic

/--
  Replace every MVar reference in `e` whose mvarId is in `subst` with the
  matching expression (typically a fvar). Used to swap cyclic-κ-mvars in
  `curr` for the corresponding ∃-binder fvars so the result can be
  abstracted into a new ∃-chain.

  Example:

1. Takes ∃ κₓ κₐ: T, P(κₓ, κₐ)
2. Turns it into one with FVar:
    Free Vars: [fκₓ, fκₐ]
    P(fκₓ, fκₐ)
3. The core fusion engine works on MVars instead — FVars are scope-bound,
  so if an acyclic κ's solution references a cyclic κ, that cyclic-κ-fvar
  would escape its introducing scope and break elaboration. MVars live
  in the global MetavarContext and don't have this problem.
4. Substitute fvars → fresh mvars, stashing the correspondence:
    Pairs:   [(?mκ_cyc, fκ_cyc), (?mκ_acy, fκ_acy)]
    Body:    P(?mκ_cyc, ?mκ_acy)
5. Solve for ?mκ_acy (acyclic). Its solution may reference ?mκ_cyc —
  that's fine, ?mκ_cyc is global and the unifier will resolve it later.
6. Residual:
    Body:    P'(?mκ_cyc)        -- ?mκ_acy is now assigned
7. ← THIS FUNCTION: feed the stashed pairs as `subst` to swap MVars → FVars:
    Body:    P'(fκ_cyc)
8. Abstract fκ_cyc into ∃:
    ∃ κ : T, P'(κ)
-/
def replaceKMvarsWithFvars
  (subst : List (MVarId × Expr)) --
  (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isMVar then
      subst.findSome? fun (m, fv) =>
        if m == sub.mvarId! then some fv else none
    else none

-- simplifyAndExists — collapse `_ ∧ False / False ∧ _ → False`,
-- `∃ x, False → False`, `True ∧ X → X`, but DO NOT touch Or-trees.
-- Used to drop dead κ-references from sol expressions (e.g. a sol_κx
-- branch like `(κy y x n p) ∧ (∃ ν, ν=y+1 ∧ False)` collapses to False
-- without breaking the goal's And-tree ↔ sol's Or-tree position mirror.
partial def simplifyAndExists (e : Expr) : Expr :=
  if e.isAppOfArity ``And 2 then
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    if l.isConstOf ``False || r.isConstOf ``False then mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  else if e.isAppOfArity ``Or 2 then
    -- Recurse into Or branches but keep the Or-node — path-mirror requires
    -- positional preservation. Branches may collapse to False internally;
    -- that's the desired "dead branch" shape.
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    mkApp2 (mkConst ``Or) l r
  else if e.isAppOfArity ``Exists 2 then
    let ty := e.appFn!.appArg!
    let body := e.appArg!
    let univrs := e.getAppFn.constLevels!
    match body with
    | .lam n t b bi =>
      let b' := simplifyAndExists b
      if b'.isConstOf ``False then mkConst ``False
      else mkApp2 (mkConst ``Exists univrs) ty (.lam n t b' bi)
    | _ => e
  else if e.isForall then
    match e with
    | .forallE n t b bi =>
      let t' := simplifyAndExists t
      let b' := simplifyAndExists b
      .forallE n t' b' bi
    | _ => e
  else e

-- Checks whether the goal `e` Expr has form `?κ a₁ a₂ .. aₙ`
def kHead? (kLams : List (KVar × Expr)) (goal : Expr) :
    Option (KVar × Expr × Array Expr) :=
  let fn := goal.getAppFn
  if fn.isMVar then
    let filtered := kLams.find? (fun (κ, _) => κ.mvarId == fn.mvarId!)
    filtered.map (fun (κ, lam) => (κ, lam, goal.getAppArgs))
  else none
