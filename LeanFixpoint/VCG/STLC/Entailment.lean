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

/-- A model for Γ under κ-assignment: every refined binding stores a value of
    the binding's base (`HasBase`) and is satisfied at that γ-value. The
    `HasBase` conjunct makes explicit what the old two-field `REnv` encoded
    structurally — that `x : {ν:b | r}` occupies a base-`b` cell — and is what
    lets `Entail.ext` round-trip a refined slot through `b.interp`. -/
@[simp]
def ModelsEnv (κ : KEnv) : REnv → TEnv → Prop
  | _, []                    => True
  | γ, (x, .refine b r) :: Γ => REnv.HasBase γ x b
                                 ∧ Refinement.interp κ r γ (REnv.get b γ x)
                                 ∧ ModelsEnv κ γ Γ
  | γ, (_, .arrow _ _)  :: Γ => ModelsEnv κ γ Γ

/-- `κ; Γ ⊢ c`: `c` (as a Lean predicate over `REnv`) holds in every model of
    Γ under κ. VCGen-produced constraints use this. -/
@[simp]
def Entail (κ : KEnv) (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ γ, ModelsEnv κ γ Γ → c γ

/-- Updating slot `x` with its current value is the identity — provided the cell
    actually holds a base-`b` value (otherwise the read defaults and the write
    re-stamps the wrong constructor). -/
theorem REnv.update_self (b : Base) (γ : REnv) (x : EVar) (hb : γ.HasBase x b) :
    REnv.update b γ x (REnv.get b γ x) = γ := by
  apply REnv.ext
  · funext y
    by_cases hxy : x = y
    · subst hxy
      cases b with
      | int  => obtain ⟨n, hn⟩ := hb
                simp [hn]
      | bool => obtain ⟨c, hc⟩ := hb
                simp [hc]
    · simp [hxy]
  · rfl

/-- ENT-EMP: `∀ γ, c γ ⟹ κ; ∅ ⊢ c`. -/
@[simp]
theorem Entail.emp {κ : KEnv} {c : REnv → Prop} (h : ∀ γ, c γ) :
    Entail κ [] c := by
  intro γ _; exact h γ

/-- ENT-EXT (predicate form): `κ; Γ ⊢ ∀v:b. r v → c[x↦v]  ⟹  κ; Γ, x:{ν:b|r} ⊢ c`.
    Instantiate with `REnv.get b γ x`, then close by `REnv.update_self`. -/
@[simp]
theorem Entail.ext {κ : KEnv} {Γ : TEnv} {x : EVar} {b : Base} {r : Refinement b}
    {c : REnv → Prop}
    (h : Entail κ Γ (fun γ => ∀ v : b.interp,
              Refinement.interp κ r γ v → c (REnv.update b γ x v))) :
    Entail κ ((x, .refine b r) :: Γ) c := by
  intro γ ⟨hb, hr, hΓ⟩
  have key := h γ hΓ (REnv.get b γ x) hr
  rw [REnv.update_self b γ x hb] at key
  exact key
