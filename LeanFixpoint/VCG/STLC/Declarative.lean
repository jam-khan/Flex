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
  | lam {κ Γ e s₁ s₂} (L : List EVar) :
      (∀ x, x ∉ L → Hastype κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x)) →
      Hastype κ Γ (.lam e) (.arrow s₁ s₂)
  | app {κ Γ e₁ y s t} :
      Hastype κ Γ e₁ (.arrow s t) →
      Hastype κ Γ (.fvar y) s →
      y ∉ t.fv →
      Hastype κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)
  | letin {κ Γ e₁ e₂ s t} (L : List EVar) :
      Hastype κ Γ e₁ s →
      (∀ x, x ∉ L → Hastype κ ((x, s) :: Γ) (e₂.openVar 0 x) t) →
      Hastype κ Γ (.letin e₁ e₂) t
  | ann {κ Γ e t} :
      Hastype κ Γ e t →
      Ty.WF Γ t →
      Hastype κ Γ (.ann e t) t
  | sub {κ Γ e s t} :
      Hastype κ Γ e s →
      Subtyp κ Γ s t →
      Hastype κ Γ e t
  | add_var {κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      x ≠ nuName → y ≠ nuName →
      Hastype κ Γ (.add (.fvar x) (.fvar y))
        (.refine .int ⟨.eqI (.fvar .int nuName)
                            (.add (.fvar .int x) (.fvar .int y))⟩)
  | leq_var {κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      x ≠ nuName → y ≠ nuName →
      Hastype κ Γ (.leq (.fvar x) (.fvar y))
        (.refine .bool ⟨.and
          (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
                (.leqI (.fvar .int x) (.fvar .int y)))
          (.imp (.leqI (.fvar .int x) (.fvar .int y))
                (.eqB (.fvar .bool nuName) (.const .bool true)))⟩)
  | not_var {κ Γ x r} :
      Γ.lookup x = some (.refine .bool r) →
      x ≠ nuName →
      Hastype κ Γ (.not (.fvar x))
        (.refine .bool ⟨.eqB (.fvar .bool nuName) (.not (.fvar .bool x))⟩)
  | and_var {κ Γ x y rx ry} :
      Γ.lookup x = some (.refine .bool rx) →
      Γ.lookup y = some (.refine .bool ry) →
      x ≠ nuName → y ≠ nuName →
      Hastype κ Γ (.and (.fvar x) (.fvar y))
        (.refine .bool ⟨.eqB (.fvar .bool nuName) (.and (.fvar .bool x) (.fvar .bool y))⟩)
  | ite {κ Γ x e₁ e₂ r t} :
      Γ.lookup x = some (.refine .bool r) →
      x ≠ nuName →
      Hastype κ ((x, .refine .bool ⟨.and r.fmla
                (.eqB (.fvar .bool nuName) (.const .bool true))⟩) :: Γ) e₁ t →
      Hastype κ ((x, .refine .bool ⟨.and r.fmla
                (.eqB (.fvar .bool nuName) (.const .bool false))⟩) :: Γ) e₂ t →
      Hastype κ Γ (.ite (.fvar x) e₁ e₂) t

/-- For fvar typing, the variable must appear in the context. -/
theorem Hastype.fvar_lookup {κ Γ x t} (h : Hastype κ Γ (.fvar x) t) :
    ∃ s, Γ.lookup x = some s := by
  -- Only var and sub (transitively) can type a free variable; proved below
  -- by structural descent but requires sorry due to LN index elaboration issue.
  generalize he : (Exp.fvar x) = e ; rw [he] at h
  induction h <;> grind

theorem EVar.not_free_in_open : x ∈ e.fv → x ∈ (Exp.openVar k y e).fv := by
    intro xf
    induction e generalizing k with
    | bvar j              => simp_all [Exp.fv]
    | fvar z              => unfold Exp.fv Exp.openVar at * ; simp_all
    | iconst i            => simp_all [Exp.fv]
    | bconst b            => simp_all [Exp.fv]
    | lam e ih | not e ih => simp_all [Exp.fv, Exp.openVar]
    | letin e₁ e₂ ih1 ih2
    | app e₁ e₂ ih1 ih2
    | add e₁ e₂ ih1 ih2
    | leq e₁ e₂ ih1 ih2
    | and e₁ e₂ ih1 ih2   =>
        simp_all [Exp.fv, Exp.openVar]
        grind
    | ite e₀ e₁ e₂ ih1 ih2 ih3 =>
        simp_all [Exp.fv, Exp.openVar]
        grind
    | ann e t ih          =>
        simp_all [Exp.fv, Exp.openVar]

/-- Deferred — see Stage 12. -/
theorem Hastype.fv_subset {κ Γ e t} (_h : Hastype κ Γ e t) :
    ∀ z ∈ Exp.fv e, ∃ t', (z, t') ∈ Γ := by
  intro z zf
  induction _h with
  | @var _ _ _ hl =>
    simp [Exp.fv] at zf
    rw [List.lookup_eq_some_iff] at hl
    grind
  | int_const | bool_const =>
    simp [Exp.fv] at zf
  | @lam Γ' e s₁ s₂ L hf ih =>
    simp [Exp.fv] at *
    obtain ⟨t', hzeq | foo⟩ := ih (EVar.fresh (L ++ e.fv)) (by grind [EVar.fresh_not_mem]) (EVar.not_free_in_open zf)
        <;> grind [EVar.fresh_not_mem]
  | @letin Γ' e₁ e₂ s t L hht hf ih1 ih2 =>
    simp [Exp.fv] at *
    rcases zf with hzf1 | hzf2
    · exact ih1 hzf1
    · obtain ⟨t', hzeq | foo⟩ := ih2 (EVar.fresh (L ++ e₂.fv)) (by grind [EVar.fresh_not_mem]) (EVar.not_free_in_open hzf2)
        <;> grind [EVar.fresh_not_mem]
  | add_var | leq_var | not_var | and_var | ite =>
    simp [Exp.fv] at zf
    rcases zf
        <;> grind [List.lookup_eq_some_iff]
  | sub => grind
  | @app Γ' e₁ y s t hht1 hht2 _hyfv ih1 ih2 =>
    simp [Exp.fv] at zf
    rcases zf with hzf1 | hzf2
    · exact ih1 hzf1
    · simp [Exp.fv] at ih2
      exact ih2 hzf2
  | @ann Γ' e t hht hWF ih =>
    simp [Exp.fv] at zf
    exact ih zf


/-- Well-typed expressions are locally closed (lc_at 0). Proved by induction on
    the typing derivation using the cofinite lam case. Deferred (Stage 12). -/
theorem Hastype.lc_at {κ Γ e t} (_h : Hastype κ Γ e t) : Exp.lc_at 0 e := by
    sorry
