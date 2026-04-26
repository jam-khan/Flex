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
        ∀ ρ, (0 ≤ ρ "x") ∧ (ρ "y" = ρ "x" + 1) → 0 ≤ ρ "y"
    which is discharged by `omega` (or LeanFixpoint).

  Design choices, with rationale:

  1. **Constraints are `REnv → Prop`, not `Prop`.** Predicates inside refinements
     can mention any program variable in scope. Threading `ρ` through `c` lets us
     speak about those variables uniformly with the predicates being modeled.

  2. **`ModelsEnv` is a recursive `Prop`, not an inductive relation.** A definition
     unfolds via `simp` directly into a conjunction of Lean Props — no induction
     principle to wrestle with at every use site. ENT-EMP / ENT-EXT become
     one-line theorems instead of constructors.

  3. **Function-typed bindings are skipped.** Refinement predicates are
     first-order: they cannot mention λ-bound names with a function type, so such
     bindings contribute no constraint to the env. (See the `arrow` case below.)

  4. **`REnv` is total (`EVar → Int`), not partial.** Out-of-scope lookups return
     0 and are never observed in valid derivations: typing rules guarantee
     predicates only mention in-scope vars. Same trick used by the While VCGen.
-/

/-- A model for Γ: an env ρ such that every refinement binding is satisfied
    (function-typed bindings are vacuously modeled). -/
@[simp]
def ModelsEnv : REnv → TEnv → Prop
  | _, []                    => True
  | ρ, (x, .refine _ r) :: Γ => r.pred ρ (ρ x) ∧ ModelsEnv ρ Γ
  | ρ, (_, .arrow ..)   :: Γ => ModelsEnv ρ Γ

/-- `Γ ⊢ c`: c holds in every env that models Γ. The Horn-clause-shaped Lean
    Prop you would hand to an SMT solver — except here Lean is the solver. -/
@[simp]
def Entail (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ ρ, ModelsEnv ρ Γ → c ρ

/-- Self-update is the identity on envs. Needed to discharge ENT-EXT, where we
    instantiate the universally-quantified value with `ρ x` and must show
    `ρ[x ↦ ρ x] = ρ`. -/
@[simp]
theorem REnv.update_self (ρ : REnv) (x : EVar) : ρ[x ↦ ρ x] = ρ := by
  funext y
  unfold REnv.update
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- ENT-EMP:  `smtvalid c  ⟹  ∅ ⊢ c`.

    With no hypotheses, "valid in Lean" *is* what entailment means. -/
@[simp]
theorem Entail.emp {c : REnv → Prop} (h : ∀ ρ, c ρ) : Entail [] c := by
  intro ρ _; exact h ρ

/-- ENT-EXT:  `Γ ⊢ ∀x:b. p x → c[x↦x]   ⟹   Γ, x:{ν:b|p} ⊢ c`.

    Extending the context with a refined binding is *exactly* introducing a
    universal quantifier guarded by the refinement — the standard Horn move. -/
@[simp]
theorem Entail.ext {Γ : TEnv} {x : EVar} {b : Base} {r : Refinement b}
    {c : REnv → Prop}
    (h : Entail Γ (fun ρ => ∀ v : b.interp, r.pred ρ v → c (ρ[x ↦ v]))) :
    Entail ((x, .refine b r) :: Γ) c := by
  intro ρ ⟨hr, hΓ⟩
  have := h ρ hΓ (ρ x) hr
  simpa using this
