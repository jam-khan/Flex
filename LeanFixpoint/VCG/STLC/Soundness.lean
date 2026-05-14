import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness

  Algorithmic VC generation is sound w.r.t. the declarative typing rules.
  Each `*_sound` theorem takes `algorithm = some c` as a precondition; mismatch
  cases close by contradiction. No satisfiability assumption needed.

  Substitution / renaming algebraic lemmas (`REnv.redirect_self`,
  `Refinement.rename_self`, `Ty.rename_self`) live in [Substitution.lean] and
  are imported transitively via `VCGen → Substitution → Syntax`.
-/

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
    by_cases hxx : x₁ = x₂
    · subst hxx
      simp only [beq_self_eq_true, if_true] at hsy
      cases hs : sub s₂ s₁ with
      | none => rw [hs] at hsy; simp at hsy
      | some c₁ =>
        cases ht : sub t₁ t₂ with
        | none => rw [hs, ht] at hsy; simp at hsy
        | some c₂ =>
          rw [hs, ht] at hsy
          -- Use symm/subst rather than `simp` here so `implyBind` stays folded in `h`.
          have h_eq : c = fun ρ => c₁ ρ ∧ implyBind x₁ s₂ c₂ ρ :=
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
    · have hb : (x₁ == x₂) = false := by simp [hxx]
      rw [hb] at hsy; simp at hsy
  | .refine .int _, .refine .bool _ | .refine .bool _, .refine .int _ =>
    simp [sub] at hsy
  | .refine _ _, .arrow _ _ _ =>
    rw [sub_refine_arrow_eq] at hsy; simp at hsy
  | .arrow _ _ _, .refine _ _ =>
    rw [sub_arrow_refine_eq] at hsy; simp at hsy
termination_by sizeOf s + sizeOf t

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
    | .add (.var x) (.var y) =>
      unfold synth at hsynth
      cases hxlk : Γ.lookup x with
      | none => rw [hxlk] at hsynth; simp at hsynth
      | some tx =>
        cases tx with
        | arrow _ _ _ => rw [hxlk] at hsynth; simp at hsynth
        | refine bx rx =>
          cases bx with
          | bool => rw [hxlk] at hsynth; simp at hsynth
          | int =>
            cases hylk : Γ.lookup y with
            | none => rw [hxlk, hylk] at hsynth; simp at hsynth
            | some ty =>
              cases ty with
              | arrow _ _ _ => rw [hxlk, hylk] at hsynth; simp at hsynth
              | refine by_ ry =>
                cases by_ with
                | bool => rw [hxlk, hylk] at hsynth; simp at hsynth
                | int =>
                  rw [hxlk, hylk] at hsynth
                  simp at hsynth
                  obtain ⟨_, ht_eq⟩ := hsynth
                  subst ht_eq
                  exact Synth.add_var hxlk hylk
    | .leq (.var x) (.var y) =>
      unfold synth at hsynth
      cases hxlk : Γ.lookup x with
      | none => rw [hxlk] at hsynth; simp at hsynth
      | some tx =>
        cases tx with
        | arrow _ _ _ => rw [hxlk] at hsynth; simp at hsynth
        | refine bx rx =>
          cases bx with
          | bool => rw [hxlk] at hsynth; simp at hsynth
          | int =>
            cases hylk : Γ.lookup y with
            | none => rw [hxlk, hylk] at hsynth; simp at hsynth
            | some ty =>
              cases ty with
              | arrow _ _ _ => rw [hxlk, hylk] at hsynth; simp at hsynth
              | refine by_ ry =>
                cases by_ with
                | bool => rw [hxlk, hylk] at hsynth; simp at hsynth
                | int =>
                  rw [hxlk, hylk] at hsynth
                  simp at hsynth
                  obtain ⟨_, ht_eq⟩ := hsynth
                  subst ht_eq
                  exact Synth.leq_var hxlk hylk
    | .not e' =>
      unfold synth at hsynth
      cases hinner : synth Γ e' with
      | none => rw [hinner] at hsynth; simp at hsynth
      | some p =>
        obtain ⟨c', ty⟩ := p
        rw [hinner] at hsynth
        cases ty with
        | arrow _ _ _ => simp at hsynth
        | refine b r =>
          cases b with
          | int => simp at hsynth
          | bool =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hsynth
            obtain ⟨hc_eq, ht_eq⟩ := hsynth
            subst ht_eq
            apply Synth.not_
            apply synth_sound _ _ _ _ hinner
            intro ρ hΓ; rw [hc_eq]; exact hc ρ hΓ
    | .and e₁' e₂' =>
      unfold synth at hsynth
      cases hinner1 : synth Γ e₁' with
      | none => rw [hinner1] at hsynth; simp at hsynth
      | some p1 =>
        obtain ⟨c₁, ty₁⟩ := p1
        rw [hinner1] at hsynth
        cases ty₁ with
        | arrow _ _ _ => simp at hsynth
        | refine b₁ r₁ =>
          cases b₁ with
          | int => simp at hsynth
          | bool =>
            cases hinner2 : synth Γ e₂' with
            | none => rw [hinner2] at hsynth; simp at hsynth
            | some p2 =>
              obtain ⟨c₂, ty₂⟩ := p2
              rw [hinner2] at hsynth
              cases ty₂ with
              | arrow _ _ _ => simp at hsynth
              | refine b₂ r₂ =>
                cases b₂ with
                | int => simp at hsynth
                | bool =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hsynth
                  obtain ⟨hc_eq, ht_eq⟩ := hsynth
                  subst ht_eq
                  apply Synth.and_
                  · apply synth_sound _ _ _ _ hinner1
                    intro ρ hΓ
                    have := hc ρ hΓ; rw [← hc_eq] at this; exact this.1
                  · apply synth_sound _ _ _ _ hinner2
                    intro ρ hΓ
                    have := hc ρ hΓ; rw [← hc_eq] at this; exact this.2
    | .app e₁ (.iconst _) | .app e₁ (.bconst _) | .app e₁ (.letin _ _ _)
    | .app e₁ (.lam _ _)  | .app e₁ (.app _ _)  | .app e₁ (.ann _ _)
    | .app e₁ (.and _ _)  | .app e₁ (.not _)    | .app e₁ (.leq _ _)
    | .app e₁ (.ite _ _ _) | .app e₁ (.add _ _)
    | .lam _ _ | .letin _ _ _ | .ite _ _ _
    | .leq e₁ (.iconst _) | .leq e₁ (.bconst _) | .leq e₁ (.letin _ _ _)
    | .leq e₁ (.lam _ _)  | .leq e₁ (.leq _ _)  | .leq e₁ (.ann _ _)
    | .leq e₁ (.and _ _)  | .leq e₁ (.not _)    | .leq e₁ (.app _ _)
    | .leq e₁ (.ite _ _ _) | .leq e₁ (.add _ _)
    | .leq (.iconst _) (.var _) | .leq (.bconst _) (.var _) | .leq (.letin _ _ _) (.var _)
    | .leq (.lam _ _) (.var _) | .leq (.leq _ _) (.var _) | .leq (.ann _ _) (.var _)
    | .leq (.and _ _) (.var _) | .leq (.not _) (.var _) | .leq (.app _ _) (.var _)
    | .leq (.ite _ _ _) (.var _) | .leq (.add _ _) (.var _)
    | .add e₁ (.iconst _) | .add e₁ (.bconst _) | .add e₁ (.letin _ _ _)
    | .add e₁ (.lam _ _)  | .add e₁ (.add _ _)  | .add e₁ (.ann _ _)
    | .add e₁ (.and _ _)  | .add e₁ (.not _)    | .add e₁ (.app _ _)
    | .add e₁ (.ite _ _ _) | .add e₁ (.leq _ _)
    | .add (.iconst _) (.var _) | .add (.bconst _) (.var _) | .add (.letin _ _ _) (.var _)
    | .add (.lam _ _) (.var _) | .add (.add _ _) (.var _) | .add (.ann _ _) (.var _)
    | .add (.and _ _) (.var _) | .add (.not _) (.var _) | .add (.app _ _) (.var _)
    | .add (.ite _ _ _) (.var _) | .add (.leq _ _) (.var _) =>
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
          cases hlk : Γ.lookup x with
          | some _ => rw [hlk] at hck; simp at hck
          | none =>
            rw [hlk] at hck
            cases hck' : check ((x, s) :: Γ) e' body with
            | none => rw [hck'] at hck; simp at hck
            | some c' =>
              rw [hck'] at hck
              obtain rfl := (Option.some.inj hck).symm
              apply Check.lam hlk
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
      cases hlk : Γ.lookup x with
      | some _ => rw [hlk] at hck; simp at hck
      | none =>
        rw [hlk] at hck
        cases hsy : synth Γ e₁ with
        | none => rw [hsy] at hck; simp at hck
        | some p =>
          rw [hsy] at hck; simp at hck
          obtain ⟨c₁, s⟩ := p
          cases hck' : check ((x, s) :: Γ) e₂ t with
          | none => rw [hck'] at hck; simp at hck
          | some c₂ =>
            rw [hck'] at hck; simp at hck; subst hck
            apply Check.letin hlk (s := s)
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
    | .not e' =>
      unfold check at hck
      cases hsy : synth Γ (.not e') with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .and e₁ e₂ =>
      unfold check at hck
      cases hsy : synth Γ (.and e₁ e₂) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .leq e₁ e₂ =>
      unfold check at hck
      cases hsy : synth Γ (.leq e₁ e₂) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .add e₁ e₂ =>
      unfold check at hck
      cases hsy : synth Γ (.add e₁ e₂) with
      | none => rw [hsy] at hck; simp at hck
      | some p =>
        rw [hsy] at hck; simp at hck; obtain ⟨c', s⟩ := p
        cases hsub : sub s t with
        | none => rw [hsub] at hck; simp at hck
        | some csub =>
          rw [hsub] at hck; simp at hck; subst hck; apply Check.sub
          · exact synth_sound _ _ _ _ hsy (fun ρ hΓ => (h ρ hΓ).1)
          · exact sub_sound _ _ _ _ hsub (fun ρ hΓ => (h ρ hΓ).2)
    | .ite e₀ e₁ e₂ =>
      unfold check at hck
      cases e₀ with
      | var x =>
        cases hlook : Γ.lookup x with
        | none => simp [hlook] at hck
        | some ty =>
          simp only [hlook] at hck
          cases ty with
          | arrow _ _ _ => simp at hck
          | refine b r =>
            cases b with
            | int => simp at hck
            | bool =>
              cases hck1 : check ((x, .refine .bool r.ite_true) :: Γ) e₁ t with
              | none => simp [hck1] at hck
              | some c₁ =>
                cases hck2 : check ((x, .refine .bool r.ite_false) :: Γ) e₂ t with
                | none => simp [hck1, hck2] at hck
                | some c₂ =>
                  simp only [hck1, hck2] at hck
                  obtain rfl := Option.some.inj hck
                  apply Check.ite hlook
                  · apply check_sound _ _ _ _ hck1
                    exact entail_implyBind_refine (fun ρ hΓ => (h ρ hΓ).1)
                  · apply check_sound _ _ _ _ hck2
                    exact entail_implyBind_refine (fun ρ hΓ => (h ρ hΓ).2)
      | iconst _ | bconst _ | lam _ _ | letin _ _ _ | ann _ _
      | app _ _ | not _ | and _ _ | leq _ _ | ite _ _ _ | add _ _ => simp at hck


  theorem synth_to_hastype {Γ : TEnv} {e : Exp} {t : Ty} :
      Synth Γ e t → Hastype Γ e t := by
    intro h
    match h with
    | .var hl        => exact .var hl
    | .int_const     => exact .int_const
    | .bool_const    => exact .bool_const
    | .ann hck       => exact .ann (check_to_hastype hck)
    | .app hsy hck   => exact .app (synth_to_hastype hsy) (check_to_hastype hck)
    | .add_var hx hy => exact .add_var hx hy
    | .leq_var hx hy => exact .leq_var hx hy
    | .not_ hsy      => exact .not_ (synth_to_hastype hsy)
    | .and_ hsy1 hsy2 => exact .and_ (synth_to_hastype hsy1) (synth_to_hastype hsy2)

  theorem check_to_hastype {Γ : TEnv} {e : Exp} {t : Ty} :
      Check Γ e t → Hastype Γ e t := by
    intro h
    match h with
    | .sub hsy hsub             => exact .sub (synth_to_hastype hsy) hsub
    | .lam hfr hck              => exact .lam hfr (by sorry) (check_to_hastype hck)
    | .letin hfr hsy hck        => exact .letin hfr (by sorry) (synth_to_hastype hsy) (check_to_hastype hck)
    | .ite hlook hck1 hck2      => exact .ite hlook (check_to_hastype hck1) (check_to_hastype hck2)

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
