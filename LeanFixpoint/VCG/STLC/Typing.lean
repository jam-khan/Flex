import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution
import LeanFixpoint.VCG.STLC.Entailment

open STLC

/-! # Bidirectional Refinement Typing (LN + deep Formula + κ-assignments)

  All judgements are indexed by `κ : KEnv` (the κ-assignment that the solver
  picks). The user typically writes `∃ κ, Check κ [] e t`.

  Binding sites use locally-nameless: `Exp.lam`/`letin` carry no binder name;
  the body has `BVar 0` for the parameter. Cofinite quantification picks fresh
  free names for opening.

  Refinements are deeply-embedded `Formula`s; `Subtyp.refine`'s constraint is
  expressed via `Refinement.subImp` (a `Formula.allI`/`allB` over `ν`).

  `Synth.not_` and `Synth.and_` are deferred (need an existential-refinement
  helper).
-/

/-! ## Subtyping  κ; Γ ⊢ s <: t -/

inductive Subtyp : KEnv → TEnv → Ty → Ty → Prop where
  /-- SUB-BASE:  `κ; Γ ⊢ ∀ν. r₁(ν) → r₂(ν)`  ⟹  `κ; Γ ⊢ {ν:b|r₁} <: {ν:b|r₂}` -/
  | refine {κ Γ b r₁ r₂} :
      EntailF κ Γ (Refinement.subImp r₁ r₂) →
      Subtyp κ Γ (.refine b r₁) (.refine b r₂)

  /-- SUB-FUN (cofinite): contravariant input, covariant output. -/
  | arrow {κ Γ s₁ t₁ s₂ t₂} (L : List EVar) :
      Subtyp κ Γ s₂ s₁ →
      (∀ x ∉ L, Subtyp κ ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x)) →
      Subtyp κ Γ (.arrow s₁ t₁) (.arrow s₂ t₂)

/-! ## Bidirectional typing -/

mutual
  -- κ; Γ ⊢ e ⇒ t : "e synthesizes type t under κ"
  inductive Synth : KEnv → TEnv → Exp → Ty → Prop where
    | var {κ Γ x t} :
        Γ.lookup x = some t →
        Synth κ Γ (.fvar x) (self x t)

    | int_const {κ Γ n} :
        Synth κ Γ (.iconst n) (prim n)

    | bool_const {κ Γ b} :
        Synth κ Γ (.bconst b) (primBool b)

    | ann {κ Γ e t} :
        Check κ Γ e t →
        Synth κ Γ (.ann e t) t

    | app {κ Γ e₁ y s t} :
        Synth κ Γ e₁ (.arrow s t) →
        Check κ Γ (.fvar y) s        →
        Synth κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)

    | leq_var {κ Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth κ Γ (.leq (.fvar x) (.fvar y))
          (.refine .bool ⟨.and
            (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
                  (.leqI (.fvar .int x) (.fvar .int y)))
            (.imp (.leqI (.fvar .int x) (.fvar .int y))
                  (.eqB (.fvar .bool nuName) (.const .bool true)))⟩)

    | add_var {κ Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth κ Γ (.add (.fvar x) (.fvar y))
          (.refine .int ⟨.eqI (.fvar .int nuName)
                              (.add (.fvar .int x) (.fvar .int y))⟩)

  -- κ; Γ ⊢ e ⇐ t : "e checks against type t under κ"
  inductive Check : KEnv → TEnv → Exp → Ty → Prop where
    | sub {κ Γ e s t} :
        Synth κ Γ e s  →
        Subtyp κ Γ s t →
        Check κ Γ e t

    | lam {κ Γ e s₁ s₂} (L : List EVar) :
        (∀ x ∉ L, Check κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x)) →
        Check κ Γ (.lam e) (.arrow s₁ s₂)

    | letin {κ Γ e₁ e₂ s t} (L : List EVar) :
        Synth κ Γ e₁ s →
        (∀ x ∉ L, Check κ ((x, s) :: Γ) (e₂.openVar 0 x) t) →
        Check κ Γ (.letin e₁ e₂) t

    | ite {κ Γ x e₁ e₂ r t} :
        Γ.lookup x = some (.refine .bool r) →
        Check κ ((x, .refine .bool ⟨.and r.fmla
                  (.eqB (.fvar .bool nuName) (.const .bool true))⟩) :: Γ) e₁ t →
        Check κ ((x, .refine .bool ⟨.and r.fmla
                  (.eqB (.fvar .bool nuName) (.const .bool false))⟩) :: Γ) e₂ t →
        Check κ Γ (.ite (.fvar x) e₁ e₂) t
end
