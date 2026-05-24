import Lean
import LeanFixpoint.Core.KVar

open Lean Meta

/-
  Simplification over expression `e`.

  Equational notation:

  ⟦ e₁ ∧ e₂ ⟧   =  False     if ⟦e₁⟧ = False  or  ⟦e₂⟧ = False
              |  ⟦e₂⟧        if ⟦e₁⟧ = True
              |  ⟦e₁⟧        if ⟦e₂⟧ = True
              |  ⟦e₁⟧ ∧ ⟦e₂⟧  otherwise
  ⟦ e₁ ∨ e₂ ⟧  =  True       if ⟦e₁⟧ = True  or  ⟦e₂⟧ = True
              |  ⟦e₂⟧        if ⟦e₁⟧ = False
              |  ⟦e₁⟧        if ⟦e₂⟧ = False
              |  ⟦e₁⟧ ∨ ⟦e₂⟧  otherwise
  ⟦ ∃ x : A, P ⟧ = False        if ⟦P⟧ = False        -- (body must be a λ)
               | ∃ x : A, ⟦P⟧   otherwise
                                -- if body is not a λ: ⟦e⟧ = e (unchanged)
                                -- NOTE: A is NOT simplified here
  ⟦ ∀ x : A, P ⟧ = True         if ⟦P⟧ = True         -- (when P uses x)
               | ∀ x : ⟦A⟧, ⟦P⟧  otherwise
  ⟦ A → B ⟧    =  True      if ⟦A⟧ = False        -- (when ∀'s body
              |  ⟦B⟧        if ⟦A⟧ = True            ignores binder ⇒
              |  True      if ⟦B⟧ = True             implication)
              |  ⟦A⟧ → ⟦B⟧  otherwise
  ⟦ e ⟧        =  e          otherwise (atoms, other connectives, etc.)
-/
partial def simplifyExpr (e : Expr) : Expr :=
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
  else if e.isForall then
    match e with
    | .forallE n t b bi =>
      let t' := simplifyExpr t
      let b' := simplifyExpr b
      if b.hasLooseBVar 0 then
        if b'.isConstOf ``True
        then mkConst ``True
        else .forallE n t' b' bi
      else
        if t'.isConstOf ``False then mkConst ``True
        else if t'.isConstOf ``True then b'
        else if b'.isConstOf ``True then mkConst ``True
        else .forallE n t' b' bi
    | _ => e
  else e
