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
