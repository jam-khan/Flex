
import Lean

open Lean Meta

/-
  Function to perform simplification on Expr.

  This allows for simplified Expr, making it
  easier to do the proof automatically.
-/
partial def simplifyExpr (e : Expr) : Expr :=
  -- Example interpretation for simplification over conjunction (∧)
  -- [e₁ ∧ e₂] := ``False if [e₁] is False ∨ ![e₂] is False
  --           |  [e₂]    if [e₁] is True
  --           |  [e₁]    if [e₂] is True
  --           |  [e₁] ∧ [e₂] otherwise
  if e.isAppOfArity ``And 2
  then
    let args  := e.getAppArgs
    let l     := simplifyExpr args[0]! -- e₁
    let r     := simplifyExpr args[1]! -- e₂
    if l.isConstOf ``False || r.isConstOf ``False
    then
      mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  --  e₁ ∨ e₂
  else if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    let l    := simplifyExpr args[0]!
    let r    := simplifyExpr args[1]!
    if l.isConstOf ``True || r.isConstOf ``True
    then
      mkConst ``True
    else if l.isConstOf ``False then r
    else if r.isConstOf ``False then l
    else mkApp2 (mkConst ``Or) l r
  -- ∃ x : A, e
  else if e.isAppOfArity ``Exists 2 then
    let args   := e.getAppArgs
    let ty     := args[0]!
    let body   := args[1]!
    let univrs := e.getAppFn.constLevels!
    match body with
    | .lam n t b bi =>
      let b' := simplifyExpr b
      if b'.isConstOf ``False then mkConst ``False
      else mkApp2 (mkConst ``Exists univrs) ty (.lam n t b' bi)
    | _ => e
  -- ∀ x : A, e (also, covers e₁ → e₂)
  else if e.isForall then
    -- .forallE n t b bi:
    -- implication if `b` has no loose bvar 0,
    -- ∀ otherwise
    match e with
    | .forallE n t b bi =>
      let t' := simplifyExpr t
      let b' := simplifyExpr b
      -- check if a de-bruijn refers to binder on ∀ x : A, ...
      -- if no binder found, it is treated
      -- as an implication
      if b.hasLooseBVar 0 then
        -- binder found and body simplified is true, return true
        -- ∀ x, e = True if [e] is ``True
        if b'.isConstOf ``True
        then mkConst ``True
        -- else ∀ x, [e]
        else .forallE n t' b' bi
      else
        -- P → Q
        if t'.isConstOf ``False then mkConst ``True
        else if t'.isConstOf ``True then b'
        else if b'.isConstOf ``True then mkConst ``True
        else .forallE n t' b' bi
    | _ => e
  else e
