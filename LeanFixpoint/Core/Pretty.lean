import Lean
import LeanFixpoint.Core.Types

open Lean

/-!
  # Pretty.lean — ToString instances for AST types

  Pretty-printing for `Pred`, `Constraint`, `RType`, `UType`, `KVar`.
  Uses precedence-based parenthesization for expressions.
-/

instance : ToString BaseTy where
  toString | .int => "Int" | .bool => "Bool"

private def parenIf (p : Bool) (s : String) : String :=
  if p then "(" ++ s ++ ")" else s


private def ppRType : RType → String
  | .tvar α           => toString α
  | .base x b r       => s!"\{{x} : {b} | {r}}"
  | .fn x dom cod     =>
      let domStr := match dom with
        | .fn _ _ _ => s!"({ppRType dom})"
        | _         => ppRType dom
      s!"({x} : {domStr}) → {ppRType cod}"
  | .forallTy α t     => s!"∀ {α}. {ppRType t}"

instance : ToString RType where toString := ppRType

private def ppUType : UType → String
  | .tvar α          => toString α
  | .base b          => toString b
  | .fn x dom cod    =>
      let domStr := match dom with
        | .fn _ _ _ => s!"({ppUType dom})"
        | _         => ppUType dom
      s!"({x} : {domStr}) → {ppUType cod}"
  | .forallTy α t    => s!"∀ {α}. {ppUType t}"

instance : ToString UType where toString := ppUType

instance : ToString KVar where
  toString k :=
    if k.params.isEmpty then toString k.name
    else
      let ps := ", ".intercalate (k.params.map toString)
      s!"{k.name}({ps})"

private def ppPred : Pred → String
  | .tru            => "⊤"
  | .fls            => "⊥"
  | .rexpr _        => "⟨expr⟩"
  | .kapp k args    =>
      let ps := ", ".intercalate (args.map fun e =>
        if e.isFVar then toString e.fvarId!.name else "⟨expr⟩")
      s!"{k.name}[{ps}]"
  | .conj p q       => s!"({ppPred p} ∧ {ppPred q})"
  | .disj p q       => s!"({ppPred p} ∨ {ppPred q})"
  | .exist x b p    => s!"∃ {x} : {b}. {ppPred p}"
  | .eqVars pi ai   => s!"{pi} = {ai}"
  | .eqExpr v e     => s!"{v} = ⟨expr⟩"

instance : ToString Pred where toString := ppPred

-- Indentation-aware printing for constraints
private def ppConstraint (indent : Nat := 0) : Constraint → String
  | .pred p        => ppPred p
  | .conj c1 c2    =>
      let pad := String.ofList (List.replicate indent ' ')
      s!"{ppConstraint indent c1}\n{pad}∧ {ppConstraint indent c2}"
  | .imp x b p c   =>
      let pad  := String.ofList (List.replicate (indent + 2) ' ')
      s!"∀ {x} : {b}.\n{pad}{ppPred p}\n{pad}⇒ {ppConstraint (indent + 2) c}"

instance : ToString Constraint where toString c := ppConstraint 0 c

-- MetaM printer — use this in the tactic for readable Expr atoms
partial def ppPredM (p : Pred) : Lean.MetaM String := do
  match p with
  | .tru          => return "⊤"
  | .fls          => return "⊥"
  | .rexpr e      => return toString (← Lean.Meta.ppExpr e)
  | .kapp k args  => do
      let ps ← args.mapM fun e =>
        if e.isFVar then return toString e.fvarId!.name
        else return toString (← Lean.Meta.ppExpr e)
      return s!"{k.name}[{", ".intercalate ps}]"
  | .conj p q     => return s!"({← ppPredM p} ∧ {← ppPredM q})"
  | .disj p q     => return s!"({← ppPredM p} ∨ {← ppPredM q})"
  | .exist x b p  => return s!"∃ {x} : {b}. {← ppPredM p}"
  | .eqVars pi ai => return s!"{pi} = {ai}"
  | .eqExpr v e   => return s!"{v} = {← Lean.Meta.ppExpr e}"

section Examples

private def fv (n : Name) : Expr := Lean.mkFVar { name := n }

-- Pred (no Expr atoms) — uses ToString directly
#eval toString (Pred.tru)
-- "⊤"
#eval toString (Pred.fls)
-- "⊥"
#eval toString (Pred.kapp ⟨`κ, [`x]⟩ [fv `a])
-- "κ[a]"
#eval toString (Pred.kapp ⟨`κ, [`x, `y]⟩ [fv `a, fv `b])
-- "κ[a, b]"
#eval toString (Pred.conj (Pred.kapp ⟨`κ, [`x]⟩ [fv `a]) Pred.tru)
-- "(κ[a] ∧ ⊤)"
#eval toString (Pred.exist `z .int (Pred.kapp ⟨`κ, [`z]⟩ [fv `z]))
-- "∃ z : Int. κ[z]"

-- Pred.rexpr shows ⟨expr⟩ (use ppPredM in MetaM for real content)
#eval toString (Pred.rexpr (Lean.mkConst ``True))
-- "⟨expr⟩"

-- Constraint — uses ToString
#eval toString (Constraint.imp `x .int Pred.tru
  (Constraint.pred (Pred.kapp ⟨`κ, [`x]⟩ [fv `x])))
-- "∀ x : Int.\n  ⊤\n  ⇒ κ[x]"

-- ppPredM — MetaM printer, shows Expr atoms via ppExpr
#eval show Lean.MetaM Unit from
  Lean.Meta.withLocalDeclD `x (Lean.mkConst ``Int) fun x =>
  Lean.Meta.withLocalDeclD `y (Lean.mkConst ``Int) fun y => do
    let eq ← Lean.Meta.mkAppM ``Eq #[x, y]
    let le ← Lean.Meta.mkAppM ``LE.le #[x, y]
    IO.println s!"{← ppPredM (Pred.rexpr eq)}"
    -- "x = y"
    IO.println s!"{← ppPredM (Pred.rexpr le)}"
    -- "x ≤ y"
    IO.println s!"{← ppPredM (Pred.conj (Pred.rexpr eq) (Pred.exist `z .int (Pred.rexpr le)))}"
    -- "(x = y ∧ ∃ z : Int. x ≤ y)"

end Examples
