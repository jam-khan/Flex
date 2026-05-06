import LeanFixpoint.VCG.STLC.Typing

open STLC

/-! # Declarative Refinement Typing for STLC

  A non-bidirectional declarative typing judgement, in the style of
  LambdaRF / SystemRF from paper `Mechanizing Refinement Types`,
  restricted to current STLC fragment.
-/

inductive Hastype : TEnv → Exp → Ty → Prop where
  -- TVar `Γ(x) = t ⇒ Γ ⊢ x : t`
  | var {Γ x t} :
      Γ.lookup x = some t →
      Hastype Γ (.var x) (self x t)
  -- TCon `integer literal`
  | int_const {Γ n} :
      Hastype Γ (.iconst n) (prim n)
  -- TBool `boolean literal`
  | bool_const {Γ b} :
      Hastype Γ (.bconst b) (primBool b)
  -- TAbs (same-binder)
  | lam {Γ x e s t} :
      Hastype ((x, s) :: Γ) e t →
      Hastype Γ (.lam x e) (.arrow x s t)
  -- TApp (ANF) `e x`
  | app {Γ e₁ y x s t} :
      Hastype Γ e₁ (.arrow x s t) →
      Hastype Γ (.var y) s        →
      Hastype Γ (.app e₁ (.var y)) (t.rename x y)
  -- TLet — synthesize binding, push obligation into body.
  | letin {Γ x e₁ e₂ s t} :
      Hastype Γ e₁ s →
      Hastype ((x, s) :: Γ) e₂ t →
      Hastype Γ (.letin x e₁ e₂) t
  -- TAnno
  | ann {Γ e t} :
      Hastype Γ e t   →
      Hastype Γ (.ann e t) t
  -- TSub
  | sub {Γ e s t} :
      Hastype Γ e s →
      Subtyp Γ s t  →
      Hastype Γ e t
  -- TLeq (ANF)
  | leq_var {Γ x y} :
      Hastype Γ (.leq (.var x) (.var y))
        (.refine .bool ⟨fun ρ v => v = decide (ρ.ints x ≤ ρ.ints y)⟩)
  -- TNot
  | not_ {Γ e r} :
      Hastype Γ e (.refine .bool r) →
      Hastype Γ (.not e)
        (.refine .bool ⟨fun ρ v => ∀ b, r.pred ρ b → v = !b⟩)
  -- TAnd
  | and_ {Γ e₁ e₂ r₁ r₂} :
      Hastype Γ e₁ (.refine .bool r₁) →
      Hastype Γ e₂ (.refine .bool r₂) →
      Hastype Γ (.and e₁ e₂)
        (.refine .bool ⟨fun ρ v => ∀ b₁ b₂, r₁.pred ρ b₁ → r₂.pred ρ b₂ → v = b₁ && b₂⟩)
  -- TIte
  | ite {Γ e₀ e₁ e₂ r t} :
      Hastype Γ e₀ (.refine .bool r) →
      Hastype Γ e₁ t →
      Hastype Γ e₂ t →
      Hastype Γ (.ite e₀ e₁ e₂) t
