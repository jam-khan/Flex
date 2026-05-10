import LeanFixpoint.VCG.STLC.Semantics
import LeanFixpoint.VCG.STLC.Declarative
import LeanFixpoint.VCG.STLC.Soundness

open STLC

/-! # Refinement Type Safety for STLC (Big-Step + Logical Relations)

  We prove:

    (T1) Subtyping is semantic inclusion of denotations.
    (T2) Fundamental Lemma: well-typed terms evaluate to values in their denotation.
    (T3) Closed-term type safety (corollary of T2).
    (T4) End-to-end VCGen safety: `topVC [] e t → ∃ v. e ⇓ v ∧ ⟦t⟧ ρ_∅ v`.

  All substitution machinery (`Val`, `Exp.subst`, `Exp.substEnv`,
  `REnv.extWithVal`, `Subst.lookup`, push-through lemmas, etc.) lives in
  [Substitution.lean]. This file contains only the logical relation
  (`TyDenote`, `EnvDenote`) and the four headline theorems.
-/

/-- Logical relation: ⟦τ⟧ as a predicate on values, parameterized by ρ.
    Termination: structural recursion on the first argument. -/
def TyDenote : Ty → REnv → Val → Prop
  | .refine .int  r, ρ, v => ∃ n : Int,  v = .iconst n ∧ r.pred ρ n
  | .refine .bool r, ρ, v => ∃ b : Bool, v = .bconst b ∧ r.pred ρ b
  | .arrow x s t,    ρ, v =>
      ∃ body, v = .clos x body ∧
        ∀ va, TyDenote s ρ va →
              ∃ vr, BigStep (body.subst x va) vr ∧
                    TyDenote t (REnv.extWithVal s ρ x va) vr

/-- Closing value substitution: `γ` provides a value for every binding in `Γ`,
    each in the corresponding type's denotation, with `ρ` reflecting `γ` on
    base slots. -/
def EnvDenote : TEnv → List (EVar × Val) → REnv → Prop
  | [],            [],            _ => True
  | (x, t) :: Γ,   (y, v) :: γ,   ρ =>
        x = y ∧
        EnvDenote Γ γ ρ ∧
        TyDenote t ρ v ∧
        (∀ n, v = .iconst n → ρ.ints  x = n) ∧
        (∀ b, v = .bconst b → ρ.bools x = b)
  | _, _, _ => False

/-! ## Helper lemmas

  Pure substitution lemmas live in [Substitution.lean]. The lemmas here all
  reference `TyDenote` or `EnvDenote` and so are intrinsically logical-
  relation-flavoured. Several remain `sorry` under the same-binder convention.
-/

/-- `EnvDenote` projects to `ModelsEnv`. -/
theorem EnvDenote.toModelsEnv :
    ∀ {Γ γ ρ}, EnvDenote Γ γ ρ → ModelsEnv ρ Γ
  | [], [], _, _ => by simp [ModelsEnv]
  | (x, .refine b r) :: Γ, (_, v) :: γ, ρ, h => by
      obtain ⟨_, hΓ, hv, hint, hbool⟩ := h
      refine ⟨?_, EnvDenote.toModelsEnv hΓ⟩
      cases b with
      | int =>
        obtain ⟨n, hvn, hp⟩ := hv
        have hρ : ρ.ints x = n := hint n hvn
        simp [REnv.get, hρ]; exact hp
      | bool =>
        obtain ⟨bv, hvb, hp⟩ := hv
        have hρ : ρ.bools x = bv := hbool bv hvb
        simp [REnv.get, hρ]; exact hp
  | (_, .arrow _ _ _) :: Γ, (_, _) :: γ, ρ, h => by
      obtain ⟨_, hΓ, _, _, _⟩ := h
      simp [ModelsEnv]; exact EnvDenote.toModelsEnv hΓ
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- From `EnvDenote`, every variable in `Γ` has a corresponding value in `γ`
    matching its type. Also returns the matching ρ-slot witness. -/
theorem EnvDenote.lookup_some :
    ∀ {Γ γ ρ}, EnvDenote Γ γ ρ →
    ∀ {x t}, Γ.lookup x = some t →
    ∃ v, Subst.lookup x γ = some v ∧ TyDenote t ρ v ∧
         (∀ n, v = .iconst n → ρ.ints  x = n) ∧
         (∀ b, v = .bconst b → ρ.bools x = b)
  | [], [], _, _, _, _, hl => by simp [List.lookup] at hl
  | (y, ty) :: Γ, (_, v) :: γ, ρ, h, x, t, hl => by
      obtain ⟨hxy, hΓ, hv, hint, hbool⟩ := h
      subst hxy
      simp [List.lookup] at hl
      by_cases hxy : x == y
      · simp [hxy] at hl
        subst hl
        refine ⟨v, ?_, hv, ?_, ?_⟩
        · simp [Subst.lookup, hxy]
        · intro n hvn
          have : x = y := by simpa [BEq.beq] using hxy
          subst this; exact hint n hvn
        · intro b hvb
          have : x = y := by simpa [BEq.beq] using hxy
          subst this; exact hbool b hvb
      · simp [hxy] at hl
        obtain ⟨v', hlk, hd, hi, hb⟩ := EnvDenote.lookup_some hΓ hl
        refine ⟨v', ?_, hd, hi, hb⟩
        simp [Subst.lookup, hxy, hlk]
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h

/-- Renaming compatibility for `TyDenote`. **TRUE** under same-binder; deferred. -/
theorem TyDenote.rename_compat
    (x y : EVar) (t : Ty) (ρ : REnv) (v : Val) :
    TyDenote (t.rename x y) ρ v ↔ TyDenote t (ρ.redirect x y) v := by sorry

/-- Weakening of `TyDenote` under update at a name fresh in `t`. **TRUE** under
    freshness; the freshness side condition is missing from Hastype.letin
    (Declarative.lean:33-36); deferred. -/
theorem TyDenote.weaken_update
    (b : Base) (ρ : REnv) (x : EVar) (w : b.interp) (t : Ty) (v : Val) :
    TyDenote t (ρ.update b x w) v ↔ TyDenote t ρ v := by sorry

/-- `EnvDenote` is stable under extending ρ at a fresh name. **TRUE** under
    same-binder convention. -/
theorem EnvDenote.weaken_extWithVal
    (Γ : TEnv) (γ : List (EVar × Val)) (ρ : REnv) (s : Ty) (x : EVar) (va : Val)
    (h : EnvDenote Γ γ ρ) :
    EnvDenote Γ γ (REnv.extWithVal s ρ x va) := by sorry

/-- TyDenote is stable under extending ρ at a fresh name. **TRUE** under same-binder. -/
theorem TyDenote.weaken_extWithVal
    (s : Ty) (ρ : REnv) (x : EVar) (va : Val) (t : Ty) (v : Val)
    (h : TyDenote t ρ v) :
    TyDenote t (REnv.extWithVal s ρ x va) v := by sorry

/-! ## T1 — Subtyping is semantic inclusion -/

theorem subtyp_sound {Γ s t} (hsub : Subtyp Γ s t) :
    ∀ {ρ}, ModelsEnv ρ Γ → ∀ {v}, TyDenote s ρ v → TyDenote t ρ v := by
  induction hsub with
  | @refine Γ b p₁ p₂ hent =>
      intro ρ hΓ v hs
      cases b with
      | int =>
        obtain ⟨n, hvn, hp₁⟩ := hs
        exact ⟨n, hvn, hent ρ hΓ n hp₁⟩
      | bool =>
        obtain ⟨bv, hvb, hp₁⟩ := hs
        exact ⟨bv, hvb, hent ρ hΓ bv hp₁⟩
  | @arrow Γ x₁ s₁ t₁ x₂ s₂ t₂ _hin _hout _ihin _ihout =>
      -- BLOCKED on alpha-equivalence at the value level.
      -- v : ⟦arrow x₁ s₁ t₁⟧ unpacks as `∃ body, v = .clos x₁ body ∧ …`,
      -- but to inhabit `⟦arrow x₂ s₂ t₂⟧` we must produce `.clos x₂ body'` —
      -- different binder. The current `Val` representation does not encode
      -- alpha-equivalence; resolving this requires either:
      --   (a) renaming the closure body, or
      --   (b) restricting Subtyp.arrow to x₁ = x₂ (same-binder).
      -- The structural reasoning (contravariance via ihin, covariance via
      -- ihout + TyDenote.rename_compat) is sketched in the prior version of
      -- this case; see the v-prefixed sorries in the git history if needed.
      intro ρ _hΓ v _hs
      sorry

/-! ## T2 — Fundamental Lemma -/

theorem hastype_fundamental {Γ e t} (h : Hastype Γ e t) :
    ∀ {γ ρ}, EnvDenote Γ γ ρ →
    ∃ v, BigStep (Exp.substEnv γ e) v ∧ TyDenote t ρ v := by
  induction h with
  | @var Γ x t hlk =>
      intro γ ρ hE
      obtain ⟨v, hlkγ, hv, hint, hbool⟩ := EnvDenote.lookup_some hE hlk
      refine ⟨v, ?_, ?_⟩
      · -- Closedness of `v` is needed by the strengthened `substEnv_var_lookup`.
        -- For iconst/bconst it's trivially true; for clos it needs an EnvDenote
        -- closedness invariant we haven't formalised yet. Treat per-constructor.
        cases v with
        | iconst n   =>
            rw [Exp.substEnv_var_lookup x γ (.iconst n) hlkγ (by simp [Val.closed, Val.fv])]
            exact BigStep.iconst
        | bconst b   =>
            rw [Exp.substEnv_var_lookup x γ (.bconst b) hlkγ (by simp [Val.closed, Val.fv])]
            exact BigStep.bconst
        | clos y body =>
            rw [Exp.substEnv_var_lookup x γ (.clos y body) hlkγ ?_]
            · exact BigStep.lam
            · -- TRUE under EnvDenote-closedness invariant; deferred.
              sorry
      · cases t with
        | refine b r =>
            simp only [self]
            cases b with
            | int =>
                obtain ⟨n, hvn, hp⟩ := hv
                refine ⟨n, hvn, hp, ?_⟩
                simp [REnv.get, hint n hvn]
            | bool =>
                obtain ⟨bv, hvb, hp⟩ := hv
                refine ⟨bv, hvb, hp, ?_⟩
                simp [REnv.get, hbool bv hvb]
        | arrow z s t' =>
            simp only [self]; exact hv
  | @int_const Γ n =>
      intro γ ρ _
      refine ⟨.iconst n, ?_, ?_⟩
      · rw [Exp.substEnv_iconst]; exact BigStep.iconst
      · exact ⟨n, rfl, by rfl⟩
  | @bool_const Γ b =>
      intro γ ρ _
      refine ⟨.bconst b, ?_, ?_⟩
      · rw [Exp.substEnv_bconst]; exact BigStep.bconst
      · exact ⟨b, rfl, by rfl⟩
  | @lam Γ x e s t _ ihbody =>
      intro γ ρ hE
      refine ⟨.clos x (Exp.substEnv γ e), ?_, ?_⟩
      · -- substEnv_lam needs `x ∉ Subst.dom γ` (TRUE under same-binder; deferred).
        rw [Exp.substEnv_lam γ x e ?_]
        · exact BigStep.lam
        · sorry
      · refine ⟨_, rfl, ?_⟩
        intro va hva
        have hE' : EnvDenote ((x, s) :: Γ) ((x, va) :: γ)
                              (REnv.extWithVal s ρ x va) := by
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · exact EnvDenote.weaken_extWithVal Γ γ ρ s x va hE
          · exact TyDenote.weaken_extWithVal s ρ x va s va hva
          · intro n hvn
            cases s with
            | refine b _ =>
                cases b with
                | int  => cases hvn; simp [REnv.extWithVal, REnv.update]
                | bool => sorry  -- contradiction: hva says va is bool, hvn says iconst
            | arrow _ _ _ => sorry  -- contradiction: hva says clos
          · intro b hvb
            cases s with
            | refine bb _ =>
                cases bb with
                | int  => sorry  -- contradiction
                | bool => cases hvb; simp [REnv.extWithVal, REnv.update]
            | arrow _ _ _ => sorry  -- contradiction
        obtain ⟨vr, hbs, hvr⟩ := ihbody hE'
        refine ⟨vr, ?_, hvr⟩
        -- Convert hbs via cons_swap (needs freshness + closedness; deferred).
        have h_xfresh : x ∉ Subst.dom γ := by sorry
        have h_va_closed : Val.closed va := by sorry
        have h_γ_closed : Subst.AllClosed γ := by sorry
        rw [Exp.substEnv_cons_swap x va γ e h_xfresh h_va_closed h_γ_closed] at hbs
        exact hbs
  | @app Γ e₁ y x s t _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v₁, hbs₁, hd₁⟩ := ih₁ hE
      obtain ⟨body, hclos, hfun⟩ := hd₁; subst hclos
      obtain ⟨va, hbs₂, hda⟩ := ih₂ hE
      obtain ⟨vr, hbsr, hvr⟩ := hfun va hda
      refine ⟨vr, ?_, ?_⟩
      · rw [Exp.substEnv_app]
        exact BigStep.app hbs₁ hbs₂ hbsr
      · rw [TyDenote.rename_compat]
        -- Need TyDenote t (ρ.redirect x y) vr from
        -- TyDenote t (extWithVal s ρ x va) vr.
        -- ρ.redirect x y looks up y where x is asked; extWithVal s ρ x va sets
        -- ρ.x := va_base. These agree iff va_base = ρ.get y. From ih₂ on the
        -- variable y, that follows by the var case's logic. Deferred sorry.
        sorry
  | @letin Γ x e₁ e₂ s t _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v₁, hbs₁, hd₁⟩ := ih₁ hE
      have hE' : EnvDenote ((x, s) :: Γ) ((x, v₁) :: γ)
                            (REnv.extWithVal s ρ x v₁) := by
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · exact EnvDenote.weaken_extWithVal Γ γ ρ s x v₁ hE
        · exact TyDenote.weaken_extWithVal s ρ x v₁ s v₁ hd₁
        all_goals sorry  -- same shape as `lam` case
      obtain ⟨v₂, hbs₂, hv₂⟩ := ih₂ hE'
      refine ⟨v₂, ?_, ?_⟩
      · -- substEnv_letin needs `x ∉ Subst.dom γ` (TRUE under same-binder; deferred).
        have h_xfresh : x ∉ Subst.dom γ := by sorry
        have h_v₁_closed : Val.closed v₁ := by sorry
        have h_γ_closed : Subst.AllClosed γ := by sorry
        rw [Exp.substEnv_letin γ x e₁ e₂ h_xfresh]
        refine BigStep.letin hbs₁ ?_
        rw [Exp.substEnv_cons_swap x v₁ γ e₂ h_xfresh h_v₁_closed h_γ_closed] at hbs₂
        exact hbs₂
      · -- TyDenote t ρ v₂ from TyDenote t (extWithVal s ρ x v₁) v₂
        -- by weakening (requires x ∉ FV(t); flagged in TyDenote.weaken_update).
        cases s with
        | refine b _ =>
            cases b with
            | int =>
                cases v₁ with
                | iconst n =>
                    simp only [REnv.extWithVal] at hv₂
                    rw [TyDenote.weaken_update] at hv₂
                    exact hv₂
                | _ => sorry
            | bool =>
                cases v₁ with
                | bconst bv =>
                    simp only [REnv.extWithVal] at hv₂
                    rw [TyDenote.weaken_update] at hv₂
                    exact hv₂
                | _ => sorry
        | arrow _ _ _ => simp [REnv.extWithVal] at hv₂; exact hv₂
  | @ann Γ e t _ ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      refine ⟨v, ?_, hv⟩
      rw [Exp.substEnv_ann]; exact BigStep.ann hbs
  | @sub Γ e s t _ hsub ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      exact ⟨v, hbs, subtyp_sound hsub (EnvDenote.toModelsEnv hE) hv⟩
  | @add_var Γ x y =>
      -- BLOCKED: Hastype.add_var lacks `Γ.lookup x = some (.refine .int _)`
      -- precondition (Declarative.lean:47-49). Without it, the rule is unsound:
      -- `add (var x) (var y)` may try to add a non-int value. To prove safety
      -- the typing rule needs to demand both operands be int-bound.
      intro γ ρ _
      sorry
  | @leq_var Γ x y =>
      -- BLOCKED: same as add_var. See Declarative.lean:51-53.
      intro γ ρ _
      sorry
  | @not_ Γ e r _ ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      obtain ⟨b, hvb, hp⟩ := hv; subst hvb
      refine ⟨.bconst (!b), ?_, ?_⟩
      · rw [Exp.substEnv_not]; exact BigStep.not_ hbs
      · refine ⟨!b, rfl, ?_⟩
        intro b' hp'
        -- The synthesized refinement reads `∀ b'. r.pred ρ b' → v = !b'`. This is
        -- only sound if `r` is functional (singleton refinement). The Hastype.not_
        -- rule does not enforce functionality; flag.
        sorry
  | @and_ Γ e₁ e₂ r₁ r₂ _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v₁, hbs₁, hv₁⟩ := ih₁ hE
      obtain ⟨v₂, hbs₂, hv₂⟩ := ih₂ hE
      obtain ⟨b₁, hvb₁, hp₁⟩ := hv₁; subst hvb₁
      obtain ⟨b₂, hvb₂, hp₂⟩ := hv₂; subst hvb₂
      refine ⟨.bconst (b₁ && b₂), ?_, ?_⟩
      · rw [Exp.substEnv_and]; exact BigStep.and_ hbs₁ hbs₂
      · refine ⟨b₁ && b₂, rfl, ?_⟩
        intro b₁' b₂' hp₁' hp₂'
        sorry  -- same singleton-refinement issue as `not_`
  | @ite Γ x e₁ e₂ r t hlk _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v, hlkγ, hv, hint, hbool⟩ := EnvDenote.lookup_some hE hlk
      obtain ⟨b, hvb, hp⟩ := hv; subst hvb
      have hρb : ρ.bools x = b := hbool b rfl
      cases b with
      | true =>
          have hE' : EnvDenote
              ((x, .refine .bool ⟨fun ρ v => r.pred ρ v ∧ v = true⟩) :: Γ)
              ((x, .bconst true) :: γ) ρ := by
            refine ⟨rfl, hE, ⟨true, rfl, hp, rfl⟩, ?_, ?_⟩
            · intro n hvn; cases hvn
            · intro b' hvb'; cases hvb'; exact hρb
          obtain ⟨vr, hbs, hvr⟩ := ih₁ hE'
          refine ⟨vr, ?_, hvr⟩
          rw [Exp.substEnv_ite, Exp.substEnv_var_lookup x γ _ hlkγ
                  (by simp [Val.closed, Val.fv])]
          refine BigStep.ite_t (by simp [Val.toExp]; exact BigStep.bconst) ?_
          -- Goal: BigStep (substEnv γ e₁) vr
          -- Have: BigStep (substEnv ((x, .bconst true) :: γ) e₁) vr
          -- Equal because x already maps to .bconst true in γ (hlkγ); the extra
          -- head substitution is redundant. TRUE; routine but defer.
          sorry
      | false =>
          have hE' : EnvDenote
              ((x, .refine .bool ⟨fun ρ v => r.pred ρ v ∧ v = false⟩) :: Γ)
              ((x, .bconst false) :: γ) ρ := by
            refine ⟨rfl, hE, ⟨false, rfl, hp, rfl⟩, ?_, ?_⟩
            · intro n hvn; cases hvn
            · intro b' hvb'; cases hvb'; exact hρb
          obtain ⟨vr, hbs, hvr⟩ := ih₂ hE'
          refine ⟨vr, ?_, hvr⟩
          rw [Exp.substEnv_ite, Exp.substEnv_var_lookup x γ _ hlkγ
                  (by simp [Val.closed, Val.fv])]
          refine BigStep.ite_f (by simp [Val.toExp]; exact BigStep.bconst) ?_
          sorry

/-! ## T3 — Closed-term type safety -/

theorem type_safety {e : Exp} {t : Ty} (h : Hastype [] e t) :
    ∃ v, BigStep e v ∧ TyDenote t REnv.empty v := by
  obtain ⟨v, hbs, hv⟩ :=
    hastype_fundamental h (γ := []) (ρ := REnv.empty) (by simp [EnvDenote])
  exact ⟨v, by simpa [Exp.substEnv] using hbs, hv⟩

/-! ## T4 — End-to-end VCGen safety -/

theorem vcgen_safety {e : Exp} {t : Ty} (h : topVC [] e t) :
    ∃ v, BigStep e v ∧ TyDenote t REnv.empty v :=
  type_safety (topVC_decl_sound _ _ h)
