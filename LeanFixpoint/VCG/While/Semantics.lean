import LeanFixpoint.VCG.While.Types

open Lean

/-! ## Expression Evaluation -/

def AExpr.eval (s : State) : AExpr → Int
  | .var x     => s x
  | .lit n     => n
  | .add a₁ a₂ => a₁.eval s + a₂.eval s
  | .sub a₁ a₂ => a₁.eval s - a₂.eval s
  | .mul a₁ a₂ => a₁.eval s * a₂.eval s

def BExpr.eval (s : State) : BExpr → Bool
  | .tt        => true
  | .ff        => false
  | .eq a₁ a₂  => decide (a₁.eval s = a₂.eval s)
  | .le a₁ a₂  => decide (a₁.eval s ≤ a₂.eval s)
  | .lt a₁ a₂  => decide (a₁.eval s < a₂.eval s)
  | .not b     => !b.eval s
  | .and b₁ b₂ => b₁.eval s && b₂.eval s
  | .or b₁ b₂  => b₁.eval s || b₂.eval s

/-! ## Big-Step Operational Semantics -/

inductive Ceval : Cmd → State → State → Prop where
  | skip {s} :
    Ceval .skip s s

  | assign {x a s} :
    Ceval (.assign x a) s (s[x ↦ a.eval s])

  | seq {c₁ s₁ s₂ c₂ s₃} :
    Ceval c₁ s₁ s₂ →
    Ceval c₂ s₂ s₃ →
    Ceval (.seq c₁ c₂) s₁ s₃

  | ite_true {c₁ s₁ s₂ b c₂} :
    b.eval s₁ = true →
    Ceval c₁ s₁ s₂ →
    Ceval (.ite b c₁ c₂) s₁ s₂

  | ite_false {c₂ s₁ s₂ b c₁} :
    b.eval s₁ = false →
    Ceval c₂ s₁ s₂ →
    Ceval (.ite b c₁ c₂) s₁ s₂

  | while_false {b c s} :
    b.eval s = false →
    Ceval (.cwhile b c) s s

  | while_true {c s₁ s₂ b s₃} :
    b.eval s₁ = true →
    Ceval c s₁ s₂ →
    Ceval (.cwhile b c) s₂ s₃ →
    Ceval (.cwhile b c) s₁ s₃

/-! ## Assertions and Hoare Triples -/

def Assertion := State → Prop

def ValidHoareTriple (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ s₁ s₂, Ceval c s₁ s₂ → P s₁ → Q s₂
