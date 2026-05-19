import LeanFixpoint.VCG.STLC.Typing

open STLC

/-! # Declarative Refinement Typing for STLC (LN + deep Formula + κ-assignments) -/

inductive Hastype : KEnv → TEnv → Exp → Ty → Prop where
  | var {κ Γ x t} :
      Γ.lookup x = some t →
      Hastype κ Γ (.fvar x) (self x t)
  | int_const {κ Γ n} :
      Hastype κ Γ (.iconst n) (prim n)
  | bool_const {κ Γ b} :
      Hastype κ Γ (.bconst b) (primBool b)
  | lam {κ Γ e s₁ s₂ x}:
      x ∉ (TEnv.dom Γ ++ (e.fv ++ s₂.fv)) →
      Hastype κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) →
      Hastype κ Γ (.lam e) (.arrow s₁ s₂)
  | app {κ Γ e₁ y s t} :
      Hastype κ Γ e₁ (.arrow s t) →
      Hastype κ Γ (.fvar y) s →
      Hastype κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)
  | letin {κ Γ e₁ e₂ s t x }:
      Hastype κ Γ e₁ s →
      x ∉ TEnv.dom Γ ++ e₂.fv ++ t.fv →
      Hastype κ ((x, s) :: Γ) (e₂.openVar 0 x) t →
      Hastype κ Γ (.letin e₁ e₂) t
  | ann {κ Γ e t} :
      Hastype κ Γ e t →
      Hastype κ Γ (.ann e t) t
  | sub {κ Γ e s t} :
      Hastype κ Γ e s →
      Subtyp κ Γ s t →
      Hastype κ Γ e t
  | add_var {κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype κ Γ (.add (.fvar x) (.fvar y))
        (.refine .int ⟨.eqI (.fvar .int nuName)
                            (.add (.fvar .int x) (.fvar .int y))⟩)
  | leq_var {κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype κ Γ (.leq (.fvar x) (.fvar y))
        (.refine .bool ⟨.and
          (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
                (.leqI (.fvar .int x) (.fvar .int y)))
          (.imp (.leqI (.fvar .int x) (.fvar .int y))
                (.eqB (.fvar .bool nuName) (.const .bool true)))⟩)
  | not_var {κ Γ x r} :
      Γ.lookup x = some (.refine .bool r) →
      Hastype κ Γ (.not (.fvar x))
        (.refine .bool ⟨.eqB (.fvar .bool nuName) (.not (.fvar .bool x))⟩)
  | and_var {κ Γ x y rx ry} :
      Γ.lookup x = some (.refine .bool rx) →
      Γ.lookup y = some (.refine .bool ry) →
      Hastype κ Γ (.and (.fvar x) (.fvar y))
        (.refine .bool ⟨.eqB (.fvar .bool nuName) (.and (.fvar .bool x) (.fvar .bool y))⟩)
  | ite {κ Γ x e₁ e₂ r t} :
      Γ.lookup x = some (.refine .bool r) →
      Hastype κ ((x, .refine .bool ⟨.and r.fmla
                (.eqB (.fvar .bool nuName) (.const .bool true))⟩) :: Γ) e₁ t →
      Hastype κ ((x, .refine .bool ⟨.and r.fmla
                (.eqB (.fvar .bool nuName) (.const .bool false))⟩) :: Γ) e₂ t →
      Hastype κ Γ (.ite (.fvar x) e₁ e₂) t

/-- Deferred — see Stage 12. -/
theorem Hastype.fv_subset {κ Γ e t} (_h : Hastype κ Γ e t) :
    ∀ z ∈ Exp.fv e, ∃ t', (z, t') ∈ Γ := by
  sorry
