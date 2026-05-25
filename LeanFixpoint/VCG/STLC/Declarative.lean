import LeanFixpoint.VCG.STLC.Typing

open STLC

/-! # Declarative Refinement Typing for STLC (LN + deep Formula + κ-assignments) -/

inductive Hastype : KEnv → TEnv → Exp → Ty → Prop where
  | var {κ Γ x t} :
      Γ.lookup x = some t →
      Ty.WFBVars t →
      Hastype κ Γ (.fvar x) (self x t)
  | int_const {κ Γ n} :
      Hastype κ Γ (.iconst n) (prim n)
  | bool_const {κ Γ b} :
      Hastype κ Γ (.bconst b) (primBool b)
  | lam {κ Γ e s₁ s₂} (L : List EVar) :
      Ty.WFBVars (.arrow s₁ s₂) →
      (∀ x, x ∉ L → Hastype κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x)) →
      Hastype κ Γ (.lam e) (.arrow s₁ s₂)
  | app {κ Γ e₁ y s t} :
      Hastype κ Γ e₁ (.arrow s t) →
      Hastype κ Γ (.fvar y) s →
      y ∉ t.fv →
      y ∉ Ty.named t →
      y ≠ nuName →
      Hastype κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)
  | letin {κ Γ e₁ e₂ s t} (L : List EVar) :
      Ty.WFBVars t →
      Hastype κ Γ e₁ s →
      (∀ x, x ∉ L → Hastype κ ((x, s) :: Γ) (e₂.openVar 0 x) t) →
      Hastype κ Γ (.letin e₁ e₂) t
  | ann {κ Γ e t} :
      Hastype κ Γ e t →
      Ty.WF Γ t →
      Ty.WFBVars t →
      Hastype κ Γ (.ann e t) t
  | sub {κ Γ e s t} :
      Hastype κ Γ e s →
      Subtyp κ Γ s t →
      Ty.WFBVars t →
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
      Ty.WFBVars t →
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
  | @var _ _ _ hl _ =>
    simp [Exp.fv] at zf
    rw [List.lookup_eq_some_iff] at hl
    grind
  | int_const | bool_const =>
    simp [Exp.fv] at zf
  | @lam Γ' e s₁ s₂ L _ hf ih =>
    simp [Exp.fv] at *
    obtain ⟨t', hzeq | foo⟩ := ih (EVar.fresh (L ++ e.fv)) (by grind [EVar.fresh_not_mem]) (EVar.not_free_in_open zf)
        <;> grind [EVar.fresh_not_mem]
  | @letin Γ' e₁ e₂ s t L _ hht hf ih1 ih2 =>
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
  | @app Γ' e₁ y s t hht1 hht2 _hyfv _hynamed _hyν ih1 ih2 =>
    simp [Exp.fv] at zf
    rcases zf with hzf1 | hzf2
    · exact ih1 hzf1
    · simp [Exp.fv] at ih2
      exact ih2 hzf2
  | @ann Γ' e t hht hWF _ ih =>
    simp [Exp.fv] at zf
    exact ih zf


/-- Well-typed expressions are locally closed (lc_at 0). Proved by induction on
    the typing derivation using the cofinite lam case. Deferred (Stage 12). -/
theorem Hastype.lc_at {κ Γ e t} (_h : Hastype κ Γ e t) : Exp.lc_at 0 e := by
  induction _h with
  | var => simp [Exp.lc_at]
  | int_const => simp [Exp.lc_at]
  | bool_const => simp [Exp.lc_at]
  | lam L _ _ ih =>
    simp only [Exp.lc_at]
    obtain ⟨x, hxL⟩ := EVar.freshWith L
    exact Exp.lc_at_of_openVar _ 0 x (ih x hxL)
  | app _ _ _ _ _ ih₁ ih₂ =>
    simp only [Exp.lc_at]; exact ⟨ih₁, ih₂⟩
  | letin L _ _ _ ih₁ ih₂ =>
    simp only [Exp.lc_at]
    obtain ⟨x, hxL⟩ := EVar.freshWith L
    exact ⟨ih₁, Exp.lc_at_of_openVar _ 0 x (ih₂ x hxL)⟩
  | ann _ _ _ ih => simp only [Exp.lc_at]; exact ih
  | sub _ _ _ ih => exact ih
  | add_var => simp [Exp.lc_at]
  | leq_var => simp [Exp.lc_at]
  | not_var => simp [Exp.lc_at]
  | and_var => simp [Exp.lc_at]
  | ite _ _ _ _ _ ih₁ ih₂ => simp only [Exp.lc_at]; exact ⟨trivial, ih₁, ih₂⟩

/-- WFBVars of `self x t` follows from WFBVars of t (self only adds fvar terms). -/
theorem Ty.WFBVars_self (x : EVar) (t : Ty) (h : Ty.WFBVars t) : Ty.WFBVars (self x t) := by
  cases t with
  | refine b r =>
    cases b <;> simp only [self, Ty.WFBVars, Ty.WFBVarCtx] at h ⊢ <;>
    intro b' k hbv <;>
    simp only [Formula.hasBVar] at hbv <;>
    rcases hbv with hbv | hbv
    · exact h b' k hbv
    · simp [Term.hasBVar] at hbv
    · exact h b' k hbv
    · simp [Term.hasBVar] at hbv
  | arrow s t => simp [self, h]

/-- WFBVars of the concrete result types for primitives. -/
theorem Ty.WFBVars_prim (n : Int) : Ty.WFBVars (prim n) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]

theorem Ty.WFBVars_primBool (b : Bool) : Ty.WFBVars (primBool b) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the add_var result type. -/
theorem Ty.WFBVars_add_result (x y : EVar) : Ty.WFBVars
    (.refine .int ⟨.eqI (.fvar .int nuName) (.add (.fvar .int x) (.fvar .int y))⟩) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the leq_var result type. -/
theorem Ty.WFBVars_leq_result (x y : EVar) : Ty.WFBVars
    (.refine .bool ⟨.and
      (.imp (.eqB (.fvar .bool nuName) (.const .bool true)) (.leqI (.fvar .int x) (.fvar .int y)))
      (.imp (.leqI (.fvar .int x) (.fvar .int y)) (.eqB (.fvar .bool nuName) (.const .bool true)))⟩) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the not_var result type. -/
theorem Ty.WFBVars_not_result (x : EVar) : Ty.WFBVars
    (.refine .bool ⟨.eqB (.fvar .bool nuName) (.not (.fvar .bool x))⟩) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the and_var result type. -/
theorem Ty.WFBVars_and_result (x y : EVar) : Ty.WFBVars
    (.refine .bool ⟨.eqB (.fvar .bool nuName) (.and (.fvar .bool x) (.fvar .bool y))⟩) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]

/-- Every type produced by a Hastype derivation is WFBVars. -/
theorem Hastype.wf_bvars {κ Γ e t} (h : Hastype κ Γ e t) : Ty.WFBVars t := by
  induction h with
  | var _ hwf => exact Ty.WFBVars_self _ _ hwf
  | int_const  => exact Ty.WFBVars_prim _
  | bool_const => exact Ty.WFBVars_primBool _
  | lam _ hwf _ => exact hwf
  | app _ _ _ _ _ ih₁ _ =>
    -- ih₁ : WFBVars (.arrow s t), need WFBVars (t.openVar 0 y)
    simp only [Ty.WFBVars, Ty.WFBVarCtx] at ih₁
    exact Ty.WFBVarCtx_openVar_last _ [] _ _ ih₁.2
  | letin _ hwf _ _ _ _ => exact hwf
  | ann _ _ hwf _ => exact hwf
  | sub _ _ hwf _ => exact hwf
  | add_var => exact Ty.WFBVars_add_result _ _
  | leq_var => exact Ty.WFBVars_leq_result _ _
  | not_var => exact Ty.WFBVars_not_result _
  | and_var => exact Ty.WFBVars_and_result _ _
  | ite _ _ hwf _ _ _ _ => exact hwf
