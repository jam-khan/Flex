import LeanFixpoint.VCG.While.Types

/-! ## Big-Step Operational Semantics -/

inductive Ceval : Cmd → State → State → Prop where
  | skip {s} :
    Ceval .skip s s

  | assign {x f s} :
    Ceval (.assign x f) s (s[x ↦ f s])

  | seq {c₁ s₁ s₂ c₂ s₃} :
    Ceval c₁ s₁ s₂ →
    Ceval c₂ s₂ s₃ →
    Ceval (.seq c₁ c₂) s₁ s₃

  | ite_true {g s₁ s₂ c₁ c₂} :
    g s₁ = true →
    Ceval c₁ s₁ s₂ →
    Ceval (.ite g c₁ c₂) s₁ s₂

  | ite_false {g s₁ s₂ c₁ c₂} :
    g s₁ = false →
    Ceval c₂ s₁ s₂ →
    Ceval (.ite g c₁ c₂) s₁ s₂

  | while_false {g c s} :
    g s = false →
    Ceval (.cwhile g c) s s

  | while_true {g c s₁ s₂ s₃} :
    g s₁ = true →
    Ceval c s₁ s₂ →
    Ceval (.cwhile g c) s₂ s₃ →
    Ceval (.cwhile g c) s₁ s₃

/-! ## Assertions and Hoare Triples -/

@[simp]
def Assertion := State → Prop

@[simp]
def ValidHoareTriple (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ s₁ s₂, Ceval c s₁ s₂ → P s₁ → Q s₂

notation "⊧" => ValidHoareTriple
