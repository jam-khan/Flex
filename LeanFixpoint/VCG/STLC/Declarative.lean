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
  -- TAbs (same-binder, no shadowing)
  | lam {Γ x e s t} :
      Γ.lookup x = none →
      Hastype ((x, s) :: Γ) e t →
      Hastype Γ (.lam x e) (.arrow x s t)
  -- TApp (ANF) `e x`
  | app {Γ e₁ y x s t} :
      Hastype Γ e₁ (.arrow x s t) →
      Hastype Γ (.var y) s        →
      Hastype Γ (.app e₁ (.var y)) (t.rename x y)
  -- TLet — synthesize binding, push obligation into body. No shadowing.
  | letin {Γ x e₁ e₂ s t} :
      Γ.lookup x = none →
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
  -- TAdd (ANF): both operands must be int-bound in Γ.
  | add_var {Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype Γ (.add (.var x) (.var y))
        (.refine .int ⟨fun ρ v => v = ρ.ints x + ρ.ints y⟩)
  -- TLeq (ANF): both operands must be int-bound in Γ.
  | leq_var {Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype Γ (.leq (.var x) (.var y))
        (.refine .bool ⟨fun ρ v => v = decide (ρ.ints x ≤ ρ.ints y)⟩)
  -- TNot: existential refinement — sound regardless of `r`'s functionality.
  | not_ {Γ e r} :
      Hastype Γ e (.refine .bool r) →
      Hastype Γ (.not e)
        (.refine .bool ⟨fun ρ v => ∃ b, r.pred ρ b ∧ v = !b⟩)
  -- TAnd: same existential trick as `not_`.
  | and_ {Γ e₁ e₂ r₁ r₂} :
      Hastype Γ e₁ (.refine .bool r₁) →
      Hastype Γ e₂ (.refine .bool r₂) →
      Hastype Γ (.and e₁ e₂)
        (.refine .bool
          ⟨fun ρ v => ∃ b₁ b₂, r₁.pred ρ b₁ ∧ r₂.pred ρ b₂ ∧ v = (b₁ && b₂)⟩)
  -- TIte (ANF, path-sensitive)
  | ite {Γ x e₁ e₂ r t} :
      Γ.lookup x = some (.refine .bool r) →
      Hastype ((x, .refine .bool ⟨fun ρ v => r.pred ρ v ∧ v = true⟩)  :: Γ) e₁ t →
      Hastype ((x, .refine .bool ⟨fun ρ v => r.pred ρ v ∧ v = false⟩) :: Γ) e₂ t →
      Hastype Γ (.ite (.var x) e₁ e₂) t

/-- A well-typed expression's free variables are bound by the typing context.
    Used by `Safety.lean` to discharge well-scopedness of constructed closures. -/
theorem Hastype.fv_subset {Γ e t} (h : Hastype Γ e t) :
    ∀ z ∈ Exp.fv e, ∃ t', (z, t') ∈ Γ := by
  -- Helper closure: `Γ.lookup x = some t → ∃ t', (x, t') ∈ Γ`.
  have lookup_mem : ∀ {Γ : TEnv} {x : EVar} {t : Ty},
      Γ.lookup x = some t → ∃ t', (x, t') ∈ Γ := by
    intro Γ x t hl
    induction Γ with
    | nil => simp [List.lookup] at hl
    | cons head tail ih =>
      obtain ⟨y, t'⟩ := head
      by_cases hxy : x = y
      · subst hxy; exact ⟨t', by simp⟩
      · have hb : (x == y) = false := by simp [hxy]
        simp only [List.lookup, hb] at hl
        obtain ⟨t'', h'⟩ := ih hl
        exact ⟨t'', by simp [h']⟩
  induction h with
  | var hl =>
      intro z hz
      simp [Exp.fv] at hz; subst hz
      exact lookup_mem hl
  | int_const => intro z hz; simp [Exp.fv] at hz
  | bool_const => intro z hz; simp [Exp.fv] at hz
  | lam _ _ ih =>
      intro z hz
      simp [Exp.fv] at hz
      obtain ⟨hz_fv, hzx⟩ := hz
      obtain ⟨t', ht'⟩ := ih z hz_fv
      simp at ht'
      rcases ht' with ⟨hzx_eq, _⟩ | h
      · exact absurd hzx_eq hzx
      · exact ⟨t', h⟩
  | @app Γ _ y _ _ _ _ _ ih₁ ih₂ =>
      intro z hz
      simp [Exp.fv] at hz
      rcases hz with hz_e₁ | hz_var
      · exact ih₁ z hz_e₁
      · have hzy : z = y := hz_var
        rw [hzy]; exact ih₂ y (by simp [Exp.fv])
  | letin _ _ _ ih₁ ih₂ =>
      intro z hz
      simp [Exp.fv] at hz
      rcases hz with hz_e₁ | ⟨hz_e₂, hzx⟩
      · exact ih₁ z hz_e₁
      · obtain ⟨t', ht'⟩ := ih₂ z hz_e₂
        simp at ht'
        rcases ht' with ⟨hzx_eq, _⟩ | h
        · exact absurd hzx_eq hzx
        · exact ⟨t', h⟩
  | ann _ ih => intro z hz; simp [Exp.fv] at hz; exact ih z hz
  | sub _ _ ih => intro z hz; exact ih z hz
  | add_var hx hy =>
      intro z hz
      simp [Exp.fv] at hz
      rcases hz with rfl | rfl
      · exact lookup_mem hx
      · exact lookup_mem hy
  | leq_var hx hy =>
      intro z hz
      simp [Exp.fv] at hz
      rcases hz with rfl | rfl
      · exact lookup_mem hx
      · exact lookup_mem hy
  | not_ _ ih => intro z hz; simp [Exp.fv] at hz; exact ih z hz
  | and_ _ _ ih₁ ih₂ =>
      intro z hz
      simp [Exp.fv] at hz
      rcases hz with hz | hz
      · exact ih₁ z hz
      · exact ih₂ z hz
  | @ite Γ x _ _ _ _ hlk _ _ ih₁ ih₂ =>
      intro z hz
      simp [Exp.fv] at hz
      -- hz : z = x ∨ z ∈ e₁.fv ∨ z ∈ e₂.fv (right-associated)
      rcases hz with rfl | hz_e₁ | hz_e₂
      · exact lookup_mem hlk
      · obtain ⟨t', ht'⟩ := ih₁ z hz_e₁
        simp at ht'
        rcases ht' with ⟨rfl, _⟩ | h
        · exact lookup_mem hlk
        · exact ⟨t', h⟩
      · obtain ⟨t', ht'⟩ := ih₂ z hz_e₂
        simp at ht'
        rcases ht' with ⟨rfl, _⟩ | h
        · exact lookup_mem hlk
        · exact ⟨t', h⟩
