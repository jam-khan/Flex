import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution

open STLC

/-! ## Entailment

  Refinements / formulas / models are all parameterized by a κ-assignment
  `κ : KEnv` (the interpretation of uninterpreted predicate symbols). The
  user typically writes `∃ κ : KEnv, Entail κ ...` and lets the solver pick.

  `Entail κ Γ c` (with `c : REnv → Prop`) is the entailment used by
  VCGen-produced `Constraint`s. Refinement subtyping is expressed semantically
  (see `Subtyp.refine` in `Typing.lean`), so no `Formula`-form entailment is
  needed now that κ lives at the `Refinement` level.
-/

/-- A model for Γ under κ-assignment: every refined binding is satisfied at
    the stored ρ-value. -/
@[simp]
def ModelsEnv (κ : KEnv) : REnv → TEnv → Prop
  | _, []                    => True
  | ρ, (x, .refine b r) :: Γ => Refinement.interp κ r ρ (REnv.get b ρ x)
                                 ∧ ModelsEnv κ ρ Γ
  | ρ, (_, .arrow _ _)  :: Γ => ModelsEnv κ ρ Γ

/-- `κ; Γ ⊢ c`: `c` (as a Lean predicate over `REnv`) holds in every model of
    Γ under κ. VCGen-produced constraints use this. -/
@[simp]
def Entail (κ : KEnv) (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ ρ, ModelsEnv κ ρ Γ → c ρ

/-- Updating slot `x` with its current value is the identity. -/
@[simp]
theorem REnv.update_self (b : Base) (ρ : REnv) (x : EVar) :
    REnv.update b ρ x (REnv.get b ρ x) = ρ := by
  cases b <;> simp only [REnv.update, REnv.get] <;> ext1 <;> funext y <;>
    by_cases hxy : x = y <;> simp [hxy]

/-- ENT-EMP: `∀ ρ, c ρ ⟹ κ; ∅ ⊢ c`. -/
@[simp]
theorem Entail.emp {κ : KEnv} {c : REnv → Prop} (h : ∀ ρ, c ρ) :
    Entail κ [] c := by
  intro ρ _; exact h ρ

/-- ENT-EXT (predicate form): `κ; Γ ⊢ ∀v:b. r v → c[x↦v]  ⟹  κ; Γ, x:{ν:b|r} ⊢ c`.
    Instantiate with `REnv.get b ρ x`, then close by `REnv.update_self`. -/
@[simp]
theorem Entail.ext {κ : KEnv} {Γ : TEnv} {x : EVar} {b : Base} {r : Refinement b}
    {c : REnv → Prop}
    (h : Entail κ Γ (fun ρ => ∀ v : b.interp,
              Refinement.interp κ r ρ v → c (REnv.update b ρ x v))) :
    Entail κ ((x, .refine b r) :: Γ) c := by
  intro ρ ⟨hr, hΓ⟩
  have key := h ρ hΓ (REnv.get b ρ x) hr
  rw [REnv.update_self] at key
  exact key
