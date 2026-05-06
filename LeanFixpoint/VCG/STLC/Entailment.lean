import LeanFixpoint.VCG.STLC.Syntax

open STLC

/-! ## Entailment Γ ⊢ c

  Captures the paper's judgment `Γ ⊢ p` ("under context Γ, constraint p is valid").
  In our shallow setup `c` is a Lean predicate over a value-environment ρ; entailment
  is "for every ρ that models Γ's refinements, c ρ holds." This collapses the
  paper's separate "SMT validity" obligation into ordinary Lean validity:

  - The paper's example
        x:int{0≤x}; y:int{y=x+1}  ⊢  0 ≤ y
    becomes the Lean Prop
        ∀ ρ, (0 ≤ Val.asBase .int (ρ "x")) ∧ ... → 0 ≤ Val.asBase .int (ρ "y")
    which is discharged by `omega` (or LeanFixpoint).

  Design choices:

  1. **`REnv = EVar → Val`** stores heterogeneous runtime values; `Val.asBase b`
     projects to `b.interp` for well-typed lookups.

  2. **`ModelsEnv` uses an existential** for refined bindings: it asserts that
     `ρ x` is literally `Val.ofBase b v` for some `v : b.interp` satisfying the
     predicate. This gives the round-trip `Val.ofBase b v = ρ x` needed by
     `Entail.ext` without a separate well-typedness invariant.

  3. **Function-typed bindings are skipped** (first-order refinements only).

  4. **`REnv` is total**, with `.int 0` as the default for out-of-scope lookups.
-/

/-- A model for Γ: an env ρ such that every refined binding `x : {ν:b|r}` has
    `ρ x = Val.ofBase b v` for some `v` satisfying `r`. -/
@[simp]
def ModelsEnv : REnv → TEnv → Prop
  | _, []                     => True
  | ρ, (x, .refine b r) :: Γ =>
      (∃ v : b.interp, ρ x = Val.ofBase b v ∧ r.pred ρ v) ∧ ModelsEnv ρ Γ
  | ρ, (_, .arrow ..)   :: Γ => ModelsEnv ρ Γ

/-- `Γ ⊢ c`: c holds in every env that models Γ. -/
@[simp]
def Entail (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ ρ, ModelsEnv ρ Γ → c ρ

/-- Self-update is the identity on envs. -/
@[simp]
theorem REnv.update_self (ρ : REnv) (x : EVar) : ρ[x ↦ ρ x] = ρ := by
  funext y
  unfold REnv.update
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- ENT-EMP: `smtvalid c ⟹ ∅ ⊢ c`. -/
@[simp]
theorem Entail.emp {c : REnv → Prop} (h : ∀ ρ, c ρ) : Entail [] c := by
  intro ρ _; exact h ρ

/-- ENT-EXT: `Γ ⊢ ∀x:b. p x → c[x↦Val.ofBase b x]  ⟹  Γ, x:{ν:b|p} ⊢ c`.

    The existential in `ModelsEnv` gives us `ρ x = Val.ofBase b v`, so we can
    substitute back and apply `REnv.update_self`. -/
@[simp]
theorem Entail.ext {Γ : TEnv} {x : EVar} {b : Base} {r : Refinement b}
    {c : REnv → Prop}
    (h : Entail Γ (fun ρ => ∀ v : b.interp, r.pred ρ v → c (ρ[x ↦ Val.ofBase b v]))) :
    Entail ((x, .refine b r) :: Γ) c := by
  intro ρ ⟨⟨v, hv_eq, hr⟩, hΓ⟩
  have key := h ρ hΓ v hr
  rw [← hv_eq] at key
  simpa using key
