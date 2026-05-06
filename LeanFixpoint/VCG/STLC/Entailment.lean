import LeanFixpoint.VCG.STLC.Syntax

open STLC

/-! ## Entailment Γ ⊢ c

  Captures the paper's judgment `Γ ⊢ p` ("under context Γ, constraint p is valid").
  In our shallow setup `c` is a Lean predicate over a value-environment ρ; entailment
  is "for every ρ that models Γ's refinements, c ρ holds."

  Design choices:

  1. **`REnv` is a structure** with separate `ints : EVar → Int` and
     `bools : EVar → Bool` fields. Refinement predicates always receive a
     concrete `Int` or `Bool` from `REnv.get`, with no `Val` wrapper.

  2. **`ModelsEnv` is a recursive `Prop`**, using `REnv.get b ρ x` to extract
     the `b`-typed value for each refined binding. This is unconditionally
     well-typed: `REnv.get b ρ x : b.interp` always.

  3. **`Entail.ext`** instantiates the universal with `REnv.get b ρ x` and
     closes by `REnv.update_self`, which holds without any well-typedness
     side condition.

  4. **Function-typed bindings are skipped** (first-order refinements only).

  5. **`REnv` is total** (`0`/`false` for out-of-scope lookups); such lookups
     are never observed in valid derivations.
-/

/-- A model for Γ: an env ρ such that every refined binding `x : {ν:b|r}`
    has `r.pred ρ (REnv.get b ρ x)` (the stored value satisfies the predicate). -/
@[simp]
def ModelsEnv : REnv → TEnv → Prop
  | _, []                     => True
  | ρ, (x, .refine b r) :: Γ => r.pred ρ (REnv.get b ρ x) ∧ ModelsEnv ρ Γ
  | ρ, (_, .arrow ..)   :: Γ => ModelsEnv ρ Γ

/-- `Γ ⊢ c`: c holds in every env that models Γ. -/
@[simp]
def Entail (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ ρ, ModelsEnv ρ Γ → c ρ

/-- Updating slot `x` with its current value is the identity. -/
@[simp]
theorem REnv.update_self (b : Base) (ρ : REnv) (x : EVar) :
    REnv.update b ρ x (REnv.get b ρ x) = ρ := by
  cases b <;> simp only [REnv.update, REnv.get] <;> ext1 <;> funext y <;>
    by_cases hxy : x = y <;> simp [hxy]

/-- ENT-EMP: `smtvalid c ⟹ ∅ ⊢ c`. -/
@[simp]
theorem Entail.emp {c : REnv → Prop} (h : ∀ ρ, c ρ) : Entail [] c := by
  intro ρ _; exact h ρ

/-- ENT-EXT: `Γ ⊢ ∀x:b. r x → c[x↦v]  ⟹  Γ, x:{ν:b|r} ⊢ c`.

    Instantiate with `REnv.get b ρ x`, then close by `REnv.update_self`. -/
@[simp]
theorem Entail.ext {Γ : TEnv} {x : EVar} {b : Base} {r : Refinement b}
    {c : REnv → Prop}
    (h : Entail Γ (fun ρ => ∀ v : b.interp, r.pred ρ v → c (REnv.update b ρ x v))) :
    Entail ((x, .refine b r) :: Γ) c := by
  intro ρ ⟨hr, hΓ⟩
  have key := h ρ hΓ (REnv.get b ρ x) hr
  rw [REnv.update_self] at *
  assumption
