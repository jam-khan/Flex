import Lean
import LeanFixpoint.Core.Types

open Lean

/-!
  # Pretty.lean — ToString instances for AST types

  Pretty-printing for `RExpr`, `Pred`, `Constraint`, `RType`, `UType`, `KVar`.
  Uses precedence-based parenthesization for expressions.
-/

instance : ToString ArithOp where
  toString | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

instance : ToString CmpOp where
  toString | .eq => "==" | .ne => "!=" | .lt => "<"
            | .le => "<=" | .gt => ">"  | .ge => ">="

instance : ToString BoolOp where
  toString | .and => "∧" | .or => "∨" | .imp => "⇒"

instance : ToString BaseTy where
  toString | .int => "Int" | .bool => "Bool"

private def parenIf (p : Bool) (s : String) : String :=
  if p then "(" ++ s ++ ")" else s

private def arithPrec : ArithOp → Nat
  | .mul | .div => 70 | .add | .sub => 60

private def cmpPrec   : CmpOp → Nat  := fun _ => 50
private def bopPrec   : BoolOp → Nat
  | .and => 40 | .or => 30 | .imp => 20

-- Precedence-aware printing for refinement expressions
mutual
  private def ppRExprPrec (prec : Nat) : RExpr → String
    | .var v       => toString v
    | .int i       => toString i
    | .bool b      => if b then "true" else "false"
    | .not r       =>
        parenIf (prec > 80) s!"¬{ppRExprPrec 81 r}"
    | .app f args  =>
        let argStr := ", ".intercalate (args.map (ppRExprPrec 0))
        s!"{f}({argStr})"
    | .arith op l r =>
        let p := arithPrec op
        parenIf (prec > p) s!"{ppRExprPrec p l} {op} {ppRExprPrec (p+1) r}"
    | .cmp op l r   =>
        let p := cmpPrec op
        parenIf (prec > p) s!"{ppRExprPrec (p+1) l} {op} {ppRExprPrec (p+1) r}"
    | .bop op l r   =>
        let p := bopPrec op
        parenIf (prec > p) s!"{ppRExprPrec (p+1) l} {op} {ppRExprPrec p r}"
end

instance : ToString RExpr where toString r := ppRExprPrec 0 r

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
  | .rexpr r        => toString r
  | .kapp k args    =>
      let ps := ", ".intercalate (args.map toString)
      s!"{k.name}[{ps}]"
  | .conj p q       => s!"({ppPred p} ∧ {ppPred q})"
  | .disj p q       => s!"({ppPred p} ∨ {ppPred q})"
  | .exist x b p    => s!"∃ {x} : {b}. {ppPred p}"

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


section Examples

def exRType : RType :=
  .base `ν .int (.cmp .gt (.var `ν) (.int 0))

def exFnType : RType :=
  .fn `x
    (.base `ν .int (.cmp .gt (.var `ν) (.int 0)))
    (.base `ν .int (.cmp .ge (.var `ν) (.var `x)))

-- A Horn constraint: ∀ x : Int. κ(x) ∧ x > 0 ⇒ κ(x+1)
def exConstraint : Constraint :=
  .imp `x .int
    (.conj (.kapp ⟨`κ, [`x]⟩ [`x]) (.rexpr (.cmp .gt (.var `x) (.int 0))))
    (.pred (.kapp ⟨`κ, [`x]⟩ [`x]))

#eval toString exRType
-- {ν : Int | ν > 0}

#eval toString exFnType
-- (x : {ν : Int | ν > 0}) → {ν : Int | ν >= x}

#eval toString exConstraint
-- ∀ x : Int.
--   (κ[x] ∧ x > 0)
--   ⇒ κ[x]

#eval IO.println (toString exRType)
#eval IO.println (toString exFnType)
#eval IO.println (toString exConstraint)

end Examples
