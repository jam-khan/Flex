import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Entailment

open STLC

/-! ## Subtyping  Γ ⊢ s <: t
  Two rules, mirroring the paper:
  - **`refine`** reduces to an entailment between the two predicates.
    The paper's alpha-renaming `p₂[v₂ := v₁]` vanishes here because
    refinement binders are explicit `pred` arguments — there is no name to rename.
  - **`arrow`** is contravariant in the input, covariant in the output, with
    the output compared under an env extended with the (shared) parameter.
    We require both arrows to use the **same binder name**, sidestepping the
    paper's `t₁[x₁ := x₂]` rename. Generalize later via `Ty.rename` if needed.
-/

inductive Subtyp : TEnv → Ty → Ty → Prop where
  /-- SUB-BASE:  Γ ⊢ ∀v. p₁ ρ v → p₂ ρ v   ⟹   Γ ⊢ {ν:b|p₁} <: {ν:b|p₂} -/
  | refine {Γ b p₁ p₂} :
      Entail Γ (fun ρ => ∀ v : b.interp, p₁ ρ v → p₂ ρ v) →
      Subtyp Γ (.refine b ⟨p₁⟩) (.refine b ⟨p₂⟩)

  /-- SUB-FUN (same-binder form):
      contravariant input, covariant output under the shared binder. -/
  | arrow {Γ x₁ s₁ t₁ x₂ s₂ t₂} :
      Subtyp Γ s₂ s₁ →
      Subtyp ((x₂, s₂) :: Γ) (t₁.rename x₁ x₂) t₂ →
      Subtyp Γ (.arrow x₁ s₁ t₁) (.arrow x₂ s₂ t₂)


-- NOTE: BELOW TYPING IS ADDED BUT WE NEED
-- TO MAKE CHOICE FOR BINDERS (LOCALLY NAMELESS etc later)
-- WHEN TRYING TO USE BELOW FOR MECHANIZATION

-- refinement type for an integer constant
@[simp]
def prim (n : Int) : Ty :=
  .refine .int ⟨fun _ v => v = n⟩

-- refinement type for a boolean constant
@[simp]
def primBool (b : Bool) : Ty :=
  .refine .bool ⟨fun _ v => v = b⟩

/-- `self x t` strengthens `t` with the self-equality `v = Val.asBase b (ρ x)`,
    relating the synthesized value to the environment binding for `x`. -/
@[simp]
def self : EVar → Ty → Ty
    | x, .refine b p    => .refine b ⟨fun ρ v => p.pred ρ v ∧ v = Val.asBase b (ρ x)⟩
    | _, .arrow x t1 t2 => .arrow x t1 t2


mutual
  -- Γ ⊢ e ⇒ t : "e synthesizes type t"
  inductive Synth : TEnv → Exp → Ty → Prop where
    /-- SYN-VAR -/
    | var {Γ x t} :
        Γ.lookup x = some t →
        Synth Γ (.var x) (self x t)

    /-- SYN-CON: integer literal gets its singleton type. -/
    | int_const {Γ n} :
        Synth Γ (.iconst n) (prim n)

    /-- SYN-BOOL: boolean literal gets its singleton type. -/
    | bool_const {Γ b} :
        Synth Γ (.bconst b) (primBool b)

    /-- SYN-ANN: an annotated term synthesizes the annotation, after checking. -/
    | ann {Γ e t} :
        Check Γ e t →
        Synth Γ (.ann e t) t

    /-- SYN-APP (ANF): function applied to a *variable* substitutes the binder. -/
    | app {Γ e₁ y x s t} :
        Synth Γ e₁ (.arrow x s t) →
        Check Γ (.var y) s        →
        Synth Γ (.app e₁ (.var y)) (t.rename x y)

  -- Γ ⊢ e ⇐ t : "e checks against type t"
  inductive Check : TEnv → Exp → Ty → Prop where
    /-- CHK-SYN (subsumption): the *only* rule that emits a subtyping VC. -/
    | sub {Γ e s t} :
        Synth Γ e s  →
        Subtyp Γ s t →
        Check Γ e t

    /-- CHK-LAM: check body against codomain in extended env. Requires same binder. -/
    | lam {Γ x e s₁ s₂} :
        Check ((x, s₁) :: Γ) e s₂ →
        Check Γ (.lam x e) (.arrow x s₁ s₂)

    /-- CHK-LET: synthesize the binding, push the obligation into the body. -/
    | letin {Γ x e₁ e₂ s t}:
        Synth Γ e₁ s →
        Check ((x, s) :: Γ) e₂ t →
        Check Γ (.letin x e₁ e₂) t
end
