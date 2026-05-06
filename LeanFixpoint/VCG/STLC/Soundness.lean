import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness

  Algorithmic VC generation is sound w.r.t. the declarative typing rules.
  Each `*_sound` theorem takes `algorithm = some c` as a precondition; mismatch
  cases close by contradiction. No satisfiability assumption needed.
-/

/-! ## Helper lemmas about `Ty.rename` -/

private theorem redirect_self (ρ : REnv) (x : EVar) : ρ.redirect x x = ρ := by
  simp only [REnv.redirect]
  ext1 <;> funext z <;> by_cases h : z = x <;> simp [h]

theorem Refinement.rename_self {b : Base} (x : EVar) (r : Refinement b) :
    r.rename x x = r := by
  obtain ⟨pred⟩ := r
  show (⟨fun ρ v => pred (ρ.redirect x x) v⟩ : Refinement b) = ⟨pred⟩
  congr 1; funext ρ v
  rw [redirect_self ρ x]

theorem Ty.rename_self (x : EVar) (t : Ty) : t.rename x x = t := by
  induction t with
  | refine b r =>
    show Ty.refine b (r.rename x x) = Ty.refine b r
    rw [Refinement.rename_self]
  | arrow z s body ihs ihb =>
    show Ty.arrow z (s.rename x x) (if z == x then body else body.rename x x)
          = Ty.arrow z s body
    rw [ihs]
    by_cases h : z = x
    · subst h; simp
    · have : (z == x) = false := by simp [h]
      simp [this, ihb]

/-! ## Helper lemmas relating `implyBind` and `Entail` -/

theorem entail_implyBind_refine
    {Γ : TEnv} {x : EVar} {b : Base} {r : Refinement b}
    {c : Constraint} :
    Entail Γ (implyBind x (.refine b r) c) → Entail ((x, .refine b r) :: Γ) c :=
  fun h => Entail.ext (by simpa [implyBind] using h)

theorem entail_implyBind_arrow
    {Γ : TEnv} {x : EVar} {x' : EVar} {s t : Ty} {c : Constraint} :
    Entail Γ (implyBind x (.arrow x' s t) c) → Entail ((x, .arrow x' s t) :: Γ) c := by
  intro h ρ hΓ
  exact h ρ hΓ

/-! ## Sub soundness -/

theorem sub_sound (Γ : TEnv) (s t : Ty) (c : Constraint) :
    sub s t = some c → Entail Γ c → Subtyp Γ s t := by
  intro hsy h
  match s, t with
  | .refine .int r₁, .refine .int r₂ =>
    rw [sub_refine_int_refine_int_eq] at hsy
    obtain rfl := Option.some.inj hsy
    exact Subtyp.refine h
  | .refine .bool r₁, .refine .bool r₂ =>
    rw [sub_refine_bool_refine_bool_eq] at hsy
    obtain rfl := Option.some.inj hsy
    exact Subtyp.refine h
  | .arrow x₁ s₁ t₁, .arrow x₂ s₂ t₂ =>
    unfold sub at hsy
    cases hs : sub s₂ s₁ with
    | none => rw [hs] at hsy; simp at hsy
    | some c₁ =>
      cases ht : sub (t₁.rename x₁ x₂) t₂ with
      | none => rw [hs, ht] at hsy; simp at hsy
      | some c₂ =>
        rw [hs, ht] at hsy
        -- Use symm/subst rather than `simp` here so `implyBind` stays folded in `h`.
        have h_eq : c = fun ρ => c₁ ρ ∧ implyBind x₂ s₂ c₂ ρ :=
          (Option.some.inj hsy).symm
        subst h_eq
        apply Subtyp.arrow
        · exact sub_sound Γ s₂ s₁ c₁ hs (fun ρ hΓ => (h ρ hΓ).1)
        · apply sub_sound _ _ _ _ ht
          match s₂ with
          | .refine b r =>
            apply Entail.ext
            intro ρ hΓ
            exact (h ρ hΓ).2
          | .arrow x' ss tt =>
            exact entail_implyBind_arrow (fun ρ hΓ => (h ρ hΓ).2)
  | .refine .int _, .refine .bool _ | .refine .bool _, .refine .int _ =>
    simp [sub] at hsy
  | .refine _ _, .arrow _ _ _ =>
    rw [sub_refine_arrow_eq] at hsy; simp at hsy
  | .arrow _ _ _, .refine _ _ =>
    rw [sub_arrow_refine_eq] at hsy; simp at hsy
termination_by sizeOf s + sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Ty.sizeOf_rename x₁ x₂ t₁; omega)

/-! ## Synth / Check soundness (mutual) -/

mutual
  theorem synth_sound (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
      synth Γ e = some (c, t) → Entail Γ c → Synth Γ e t := by
    intro hsynth hc
    match e with
    | .var x =>
      unfold synth at hsynth
      rw [Option.map_eq_some_iff] at hsynth
      obtain ⟨t', hl, hp⟩ := hsynth
      have ht : t = self x t' := (Prod.mk.inj hp).2.symm
      subst ht
      exact Synth.var hl
    | .iconst n =>
      unfold synth at hsynth
      simp at hsynth
      obtain ⟨_, ht_eq⟩ := hsynth
      subst ht_eq
      exact Synth.int_const
    | .bconst b =>
      unfold synth at hsynth
      simp at hsynth
      obtain ⟨_, ht_eq⟩ := hsynth
      subst ht_eq
      exact Synth.bool_const
    | .ann e' t' =>
      unfold synth at hsynth
      cases hck : check Γ e' t' with
      | none => rw [hck] at hsynth; simp at hsynth
      | some c' =>
        rw [hck] at hsynth
        simp at hsynth
        obtain ⟨hc_eq, ht_eq⟩ := hsynth
        subst ht_eq
        apply Synth.ann
        apply check_sound _ _ _ _ hck
        rw [hc_eq]; exact hc
    | .app e₁ (.var y) =>
      unfold synth at hsynth
      cases hsy : synth Γ e₁ with
      | none => rw [hsy] at hsynth; simp at hsynth
      | some p =>
        obtain ⟨cf, tf⟩ := p
        cases tf with
        | refine _ _ => rw [hsy] at hsynth; simp at hsynth
        | arrow x s t' =>
          rw [hsy] at hsynth
          dsimp only at hsynth
          cases hck : check Γ (.var y) s with
          | none => rw [hck] at hsynth; simp at hsynth
          | some c' =>
            rw [hck] at hsynth
            simp at hsynth
            obtain ⟨hc_eq, ht_eq⟩ := hsynth
            subst ht_eq
            apply Synth.app
            · apply synth_sound _ _ _ _ hsy
              intro ρ hΓ; have := hc ρ hΓ; rw [← hc_eq] at this; exact this.1
            · apply check_sound _ _ _ _ hck
              intro ρ hΓ; have := hc ρ hΓ; rw [← hc_eq] at this; exact this.2
    | .app e₁ (.iconst _) | .app e₁ (.bconst _) | .app e₁ (.letin _ _ _)
    | .app e₁ (.lam _ _)  | .app e₁ (.app _ _)  | .app e₁ (.ann _ _)
    | .lam _ _ | .letin _ _ _ =>
      unfold synth at hsynth; simp at hsynth

  theorem check_sound (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint) :
      check Γ e t = some c → Entail Γ c → Check Γ e t := by
    intro hck h
    match e with
    | .lam x e' =>
      match t with
      | .arrow x' s body =>
        unfold check at hck
        by_cases hxx : x = x'
        · subst hxx
          simp only [beq_self_eq_true, if_true] at hck
          cases hck' : check ((x, s) :: Γ) e' body with
          | none => rw [hck'] at hck; simp at hck
          | some c' =>
            rw [hck'] at hck
            obtain rfl := (Option.some.inj hck).symm
            apply Check.lam
            apply check_sound _ _ _ _ hck'
            match s with
            | .refine b r => exact Entail.ext h
            | .arrow x'' ss tt => exact entail_implyBind_arrow h
        · have : (x == x') = false := by simp [hxx]
          rw [this] at hck; simp at hck
      | .refine b r =>
        unfold check at hck; simp [synth] at hck
    | .letin x e₁ e₂ =>
      unfold check at hck
      cases hsy : synth Γ e₁ with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck
        obtain ⟨c₁, s⟩ := p
        cases hck' : check ((x, s) :: Γ) e₂ t with
        | none => rw [hck'] at hck; simp at hck
        | some c₂ =>
          rw [hck'] at hck; simp at hck; subst hck
          apply Check.letin (s := s)
          · apply synth_sound _ _ _ _ hsy
            intro ρ hΓ; exact (h ρ hΓ).1
          · apply check_sound _ _ _ _ hck'
            match s with
            | .refine b r =>
              apply Entail.ext; intro ρ hΓ
              simp [REnv.update] ; exact (h ρ hΓ).2
            | .arrow x' ss tt =>
              apply entail_implyBind_arrow; intro ρ hΓ; exact (h ρ hΓ).2
    -- Catch-all cases (Chk-Syn): synthesize then subtype.
    -- Each case names the concrete synth call to avoid variable-substitution issues.
    | .var x =>
      unfold check at hck
      cases hsy : synth Γ (.var x) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .iconst n =>
      unfold check at hck
      cases hsy : synth Γ (.iconst n) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .bconst b =>
      unfold check at hck
      cases hsy : synth Γ (.bconst b) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .ann e' t' =>
      unfold check at hck
      cases hsy : synth Γ (.ann e' t') with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .app e₁ e₂ =>
      unfold check at hck
      cases hsy : synth Γ (.app e₁ e₂) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)

  theorem synth_to_hastype {Γ : TEnv} {e : Exp} {t : Ty} :
      Synth Γ e t → Hastype Γ e t := by
    intro h
    match h with
    | .var hl        => exact .var hl
    | .int_const     => exact .int_const
    | .bool_const    => exact .bool_const
    | .ann hck       => exact .ann (check_to_hastype hck)
    | .app hsy hck   => exact .app (synth_to_hastype hsy) (check_to_hastype hck)

  theorem check_to_hastype {Γ : TEnv} {e : Exp} {t : Ty} :
      Check Γ e t → Hastype Γ e t := by
    intro h
    match h with
    | .sub hsy hsub  => exact .sub (synth_to_hastype hsy) hsub
    | .lam hck       => exact .lam (check_to_hastype hck)
    | .letin hsy hck => exact .letin (synth_to_hastype hsy) (check_to_hastype hck)

end

theorem synth_decl_sound (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
    synth Γ e = some (c, t) → Entail Γ c → Hastype Γ e t :=
  fun h hc => synth_to_hastype (synth_sound Γ e c t h hc)

theorem check_decl_sound (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint) :
    check Γ e t = some c → Entail Γ c → Hastype Γ e t :=
  fun h hc => check_to_hastype (check_sound Γ e t c h hc)

theorem topVC_decl_sound (e : Exp) (t : Ty) :
    topVC [] e t → Hastype [] e t := by
  unfold topVC
  cases hck : check [] e t with
  | none   => intro hf; exact hf.elim
  | some c => intro h; exact check_decl_sound [] e t c hck (Entail.emp h)
