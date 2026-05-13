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

    The arrow case demands the closure value be **closed** as a value
    (`Val.fv = []` — i.e. body's free variables are at most the binder).
    This invariant is what lets us discharge the closedness preconditions on
    `Exp.substEnv_*` from `Substitution.lean` without separate machinery.

    Termination: structural recursion on the first argument. -/
def TyDenote : Ty → REnv → Val → Prop
  | .refine .int  r, ρ, v => ∃ n : Int,  v = .iconst n ∧ r.pred ρ n
  | .refine .bool r, ρ, v => ∃ b : Bool, v = .bconst b ∧ r.pred ρ b
  | .arrow x s t,    ρ, v =>
      ∃ body, v = .clos x body ∧ Val.closed (.clos x body) ∧
        ∀ va, TyDenote s ρ va →
              ∃ vr, BigStep (body.subst x va) vr ∧
                    TyDenote t (REnv.extWithVal s ρ x va) vr

/-- Closing value substitution: `γ` provides a value for every binding in `Γ`,
    each in the corresponding type's denotation, with `ρ` reflecting `γ` on
    base slots. We deliberately *don't* require `γ`'s keys be distinct: the
    `ite` case adds a refining head entry that shadows an existing binding
    for the scrutinee, so the same name appears twice in `γ` with consistent
    values. List-lookup semantics (first-match) keeps this sound. -/
def EnvDenote : TEnv → List (EVar × Val) → REnv → Prop
  | [],            [],            _ => True
  | (x, t) :: Γ,   (y, v) :: γ,   ρ =>
        x = y ∧
        EnvDenote Γ γ ρ ∧
        TyDenote t ρ v ∧
        (∀ n, v = .iconst n → ρ.ints  x = n) ∧
        (∀ b, v = .bconst b → ρ.bools x = b)
  | _, _, _ => False

/-- Every value in the denotation is closed (refinement-base values are
    iconst/bconst, arrow values are required closed). -/
theorem TyDenote.closed {t : Ty} {ρ : REnv} {v : Val} (h : TyDenote t ρ v) :
    Val.closed v := by
  cases t with
  | refine b r =>
    cases b with
    | int  => obtain ⟨n,  hvn, _⟩ := h; subst hvn; simp [Val.closed, Val.fv]
    | bool => obtain ⟨bv, hvb, _⟩ := h; subst hvb; simp [Val.closed, Val.fv]
  | arrow x s t =>
    obtain ⟨_, hvc, hcl, _⟩ := h
    subst hvc
    exact hcl

/-! ## Helper lemmas

  Pure substitution lemmas live in [Substitution.lean]. The lemmas here all
  reference `TyDenote` or `EnvDenote` and so are intrinsically logical-
  relation-flavoured.
  Several remain `srry` under the same-binder convention.
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

/-- All values in γ are closed (derived from `TyDenote.closed` for each entry). -/
theorem EnvDenote.allClosed :
    ∀ {Γ γ ρ}, EnvDenote Γ γ ρ → Subst.AllClosed γ
  | [], [], _, _ => True.intro
  | (_, _) :: _, (_, v) :: γ, _, h => by
      obtain ⟨_, hΓ, hv, _, _⟩ := h
      exact ⟨TyDenote.closed hv, EnvDenote.allClosed hΓ⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- Under `EnvDenote Γ γ ρ`, every key appearing in `Γ` appears in `γ`. Used
    by the `lam` Val.closed proof to discharge free-variable obligations. -/
theorem EnvDenote.mem_dom :
    ∀ {Γ γ ρ}, EnvDenote Γ γ ρ → ∀ {z t'}, (z, t') ∈ Γ → z ∈ Subst.dom γ
  | [], [], _, _, _, _, hm => by simp at hm
  | (y, _) :: Γ', (_, _) :: γ', ρ, h, z, t', hm => by
      obtain ⟨hxy, hΓ, _, _, _⟩ := h
      subst hxy
      simp at hm
      rcases hm with ⟨rfl, _⟩ | rest
      · simp [Subst.dom]
      · simp [Subst.dom]; exact Or.inr (EnvDenote.mem_dom hΓ rest)
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h

/-- Under `EnvDenote Γ γ ρ`, if `x` is fresh in `Γ` then it's fresh in `γ`.
    Since `γ`'s domain may now contain duplicates (head-shadowing in `ite`),
    we prove this by induction; the precondition's `Γ.lookup x = none`
    forces every `γ` entry's key to differ from `x`. -/
theorem EnvDenote.lookup_none_dom :
    ∀ {Γ γ ρ}, EnvDenote Γ γ ρ → ∀ {x}, Γ.lookup x = none → x ∉ Subst.dom γ
  | [], [], _, _, _, _ => by simp [Subst.dom]
  | (y, _) :: Γ, (_, _) :: γ, ρ, h, x, hl => by
      obtain ⟨hxy, hΓ, _, _, _⟩ := h
      subst hxy
      simp only [List.lookup] at hl
      by_cases hxy' : x = y
      · subst hxy'; simp at hl
      · have hxy_b : (x == y) = false := by simp [hxy']
        rw [hxy_b] at hl
        simp [Subst.dom]
        refine ⟨hxy', ?_⟩
        exact EnvDenote.lookup_none_dom hΓ hl
  | [], _ :: _, _, h, _, _ => by cases h
  | _ :: _, [], _, h, _, _ => by cases h

/-- From `EnvDenote`, every variable in `Γ` has a corresponding value in `γ`
    matching its type. Also returns the matching ρ-slot witness and the value's
    closedness. -/
theorem EnvDenote.lookup_some :
    ∀ {Γ γ ρ}, EnvDenote Γ γ ρ →
    ∀ {x t}, Γ.lookup x = some t →
    ∃ v, Subst.lookup x γ = some v ∧ TyDenote t ρ v ∧ Val.closed v ∧
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
        refine ⟨v, ?_, hv, TyDenote.closed hv, ?_, ?_⟩
        · simp [Subst.lookup, hxy]
        · intro n hvn
          have : x = y := by simpa [BEq.beq] using hxy
          subst this; exact hint n hvn
        · intro b hvb
          have : x = y := by simpa [BEq.beq] using hxy
          subst this; exact hbool b hvb
      · simp [hxy] at hl
        obtain ⟨v', hlk, hd, hcl, hi, hb⟩ := EnvDenote.lookup_some hΓ hl
        refine ⟨v', ?_, hd, hcl, hi, hb⟩
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

/-- `ModelsEnv` is stable under extending ρ at a fresh name. **TRUE** under
    shallow-refinement weakening; deferred (same blocker as the other
    `weaken_*` helpers). -/
theorem ModelsEnv.weaken_extWithVal
    (Γ : TEnv) (ρ : REnv) (s : Ty) (x : EVar) (va : Val)
    (h : ModelsEnv ρ Γ) :
    ModelsEnv (REnv.extWithVal s ρ x va) Γ := by sorry

/-- If `x` is already bound in `γ` to a closed value `v` (and `γ` itself is
    closed pointwise), then prepending another `(x, v)` to `γ` doesn't change
    the result of `substEnv`. Used in the `ite` case where the scrutinee
    variable is already in the value substitution. -/
private theorem Exp.substEnv_cons_lookup
    {x : EVar} {v : Val} (γ : List (EVar × Val))
    (hlk : Subst.lookup x γ = some v) (hv : Val.closed v) (hγ : Subst.AllClosed γ)
    (e : Exp) :
    Exp.substEnv ((x, v) :: γ) e = Exp.substEnv γ e := by
  induction γ generalizing e with
  | nil => simp [Subst.lookup] at hlk
  | cons head tail ih =>
    obtain ⟨y, w⟩ := head
    obtain ⟨hw, hγ'⟩ := hγ
    have hvfv : Val.fv v = [] := hv
    have hwfv : Val.fv w = [] := hw
    show Exp.substEnv tail ((e.subst x v).subst y w) = Exp.substEnv tail (e.subst y w)
    by_cases hxy : x = y
    · subst hxy
      simp only [Subst.lookup, beq_self_eq_true, if_true, Option.some.injEq] at hlk
      -- hlk : w = v; rewrite goal to use w
      rw [← hlk]
      rw [Exp.subst_subst_eq x w w e (by rw [hwfv]; simp)]
    · have hxy_b : (x == y) = false := by simp [hxy]
      simp only [Subst.lookup, hxy_b] at hlk
      rw [Exp.subst_subst_swap x y v w e hxy
            (by rw [hvfv]; simp)
            (by rw [hwfv]; simp)]
      exact ih hlk hγ' _

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
  | @arrow Γ x s₁ t₁ s₂ t₂ hin _hout ihin ihout =>
      intro ρ hΓ v hv
      obtain ⟨body, hbody, hcl, hfun⟩ := hv; subst hbody
      refine ⟨body, rfl, hcl, ?_⟩
      intro va hva
      have hva_s₁ : TyDenote s₁ ρ va := ihin hΓ hva
      obtain ⟨vr, hbsr, hvr⟩ := hfun va hva_s₁
      refine ⟨vr, hbsr, ?_⟩
      -- extWithVal only inspects the outer shape (refine/arrow) and base; the
      -- refinement predicate is ignored. Subtyp Γ s₂ s₁ forces matching shape,
      -- so the two ext-envs agree.
      have hExt : REnv.extWithVal s₁ ρ x va = REnv.extWithVal s₂ ρ x va := by
        cases hin with
        | @refine _ b _ _ _ => cases b <;> cases va <;> rfl
        | arrow _ _ => rfl
      rw [hExt] at hvr
      have hΓ' : ModelsEnv (REnv.extWithVal s₂ ρ x va) ((x, s₂) :: Γ) := by
        have hva' : TyDenote s₂ (REnv.extWithVal s₂ ρ x va) va :=
          TyDenote.weaken_extWithVal s₂ ρ x va s₂ va hva
        have htail : ModelsEnv (REnv.extWithVal s₂ ρ x va) Γ :=
          ModelsEnv.weaken_extWithVal Γ ρ s₂ x va hΓ
        cases s₂ with
        | refine b _ =>
          cases b with
          | int =>
            obtain ⟨n, hvn, hp⟩ := hva'
            subst hvn
            simp only [REnv.extWithVal] at hp
            refine ⟨?_, htail⟩
            simpa [REnv.get, REnv.extWithVal, REnv.update] using hp
          | bool =>
            obtain ⟨bv, hvb, hp⟩ := hva'
            subst hvb
            simp only [REnv.extWithVal] at hp
            refine ⟨?_, htail⟩
            simpa [REnv.get, REnv.extWithVal, REnv.update] using hp
        | arrow _ _ _ =>
          simp only [ModelsEnv]
          exact htail
      exact ihout hΓ' hvr

/-! ## T2 — Fundamental Lemma -/

theorem hastype_fundamental {Γ e t} (h : Hastype Γ e t) :
    ∀ {γ ρ}, EnvDenote Γ γ ρ →
    ∃ v, BigStep (Exp.substEnv γ e) v ∧ TyDenote t ρ v := by
  induction h with
  | @var Γ x t hlk =>
      intro γ ρ hE
      obtain ⟨v, hlkγ, hv, hcl, hint, hbool⟩ := EnvDenote.lookup_some hE hlk
      refine ⟨v, ?_, ?_⟩
      · rw [Exp.substEnv_var_lookup x γ v hlkγ hcl]
        cases v with
        | iconst n    => exact BigStep.iconst
        | bconst b    => exact BigStep.bconst
        | clos y body => exact BigStep.lam
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
  | @lam Γ x e s t hfresh hbody ihbody =>
      intro γ ρ hE
      -- Freshness now provided by `Hastype.lam`'s `Γ.lookup x = none` premise.
      have h_xfresh : x ∉ Subst.dom γ := EnvDenote.lookup_none_dom hE hfresh
      have h_γ_closed : Subst.AllClosed γ := EnvDenote.allClosed hE
      refine ⟨.clos x (Exp.substEnv γ e), ?_, ?_⟩
      · rw [Exp.substEnv_lam γ x e h_xfresh]
        exact BigStep.lam
      · -- TyDenote (.arrow x s t) ρ (.clos x (substEnv γ e))
        refine ⟨_, rfl, ?_, ?_⟩
        · -- Val.closed: every free var of (substEnv γ e) equals the binder x.
          show Val.fv (.clos x (Exp.substEnv γ e)) = []
          simp only [Val.fv]
          apply List.filter_eq_nil_iff.mpr
          intro z hz
          obtain ⟨hz_e, hz_dom⟩ := Exp.substEnv_fv_subset γ e h_γ_closed z hz
          obtain ⟨t', ht'⟩ := hbody.fv_subset z hz_e
          simp at ht'
          rcases ht' with ⟨rfl, _⟩ | hin
          · simp
          · exact absurd (EnvDenote.mem_dom hE hin) hz_dom
        · intro va hva
          have h_va_closed : Val.closed va := TyDenote.closed hva
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
                  | bool =>
                      -- Contradiction: hva says va is bool but hvn says iconst.
                      obtain ⟨_, hvb, _⟩ := hva
                      rw [hvn] at hvb; cases hvb
              | arrow _ _ _ =>
                  -- Contradiction: hva says va is a closure.
                  obtain ⟨_, hvc, _, _⟩ := hva
                  rw [hvn] at hvc; cases hvc
            · intro b hvb
              cases s with
              | refine bb _ =>
                  cases bb with
                  | int  =>
                      obtain ⟨_, hvi, _⟩ := hva
                      rw [hvb] at hvi; cases hvi
                  | bool => cases hvb; simp [REnv.extWithVal, REnv.update]
              | arrow _ _ _ =>
                  obtain ⟨_, hvc, _, _⟩ := hva
                  rw [hvb] at hvc; cases hvc
          obtain ⟨vr, hbs, hvr⟩ := ihbody hE'
          refine ⟨vr, ?_, hvr⟩
          rw [Exp.substEnv_cons_swap x va γ e h_xfresh h_va_closed h_γ_closed] at hbs
          exact hbs
  | @app Γ e₁ y x s t _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v₁, hbs₁, hd₁⟩ := ih₁ hE
      obtain ⟨body, hclos, _hcl, hfun⟩ := hd₁; subst hclos
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
        -- variable y, that follows by the var case's logic.
        sorry
  | @letin Γ x e₁ e₂ s t hfresh _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v₁, hbs₁, hd₁⟩ := ih₁ hE
      have h_xfresh : x ∉ Subst.dom γ := EnvDenote.lookup_none_dom hE hfresh
      have h_v₁_closed : Val.closed v₁ := TyDenote.closed hd₁
      have h_γ_closed : Subst.AllClosed γ := EnvDenote.allClosed hE
      have hE' : EnvDenote ((x, s) :: Γ) ((x, v₁) :: γ)
                            (REnv.extWithVal s ρ x v₁) := by
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · exact EnvDenote.weaken_extWithVal Γ γ ρ s x v₁ hE
        · exact TyDenote.weaken_extWithVal s ρ x v₁ s v₁ hd₁
        · intro n hvn
          cases s with
          | refine b _ =>
              cases b with
              | int  => cases hvn; simp [REnv.extWithVal, REnv.update]
              | bool =>
                  obtain ⟨_, hvb, _⟩ := hd₁
                  rw [hvn] at hvb; cases hvb
          | arrow _ _ _ =>
              obtain ⟨_, hvc, _, _⟩ := hd₁
              rw [hvn] at hvc; cases hvc
        · intro b hvb
          cases s with
          | refine bb _ =>
              cases bb with
              | int  =>
                  obtain ⟨_, hvi, _⟩ := hd₁
                  rw [hvb] at hvi; cases hvi
              | bool => cases hvb; simp [REnv.extWithVal, REnv.update]
          | arrow _ _ _ =>
              obtain ⟨_, hvc, _, _⟩ := hd₁
              rw [hvb] at hvc; cases hvc
      obtain ⟨v₂, hbs₂, hv₂⟩ := ih₂ hE'
      refine ⟨v₂, ?_, ?_⟩
      · rw [Exp.substEnv_letin γ x e₁ e₂ h_xfresh]
        refine BigStep.letin hbs₁ ?_
        rw [Exp.substEnv_cons_swap x v₁ γ e₂ h_xfresh h_v₁_closed h_γ_closed] at hbs₂
        exact hbs₂
      · -- TyDenote t ρ v₂ from TyDenote t (extWithVal s ρ x v₁) v₂
        -- by weakening (requires x ∉ FV(t); flagged in TyDenote.weaken_update).
        cases s with
        | refine b _ =>
            cases b with
            | int =>
                obtain ⟨n, hvn, _⟩ := hd₁; subst hvn
                simp only [REnv.extWithVal] at hv₂
                rw [TyDenote.weaken_update] at hv₂
                exact hv₂
            | bool =>
                obtain ⟨bv, hvb, _⟩ := hd₁; subst hvb
                simp only [REnv.extWithVal] at hv₂
                rw [TyDenote.weaken_update] at hv₂
                exact hv₂
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
  | @add_var Γ x y r₁ r₂ hxlk hylk =>
      intro γ ρ hE
      obtain ⟨vx, hlkx, hvx, hvx_cl, hintx, _⟩ := EnvDenote.lookup_some hE hxlk
      obtain ⟨vy, hlky, hvy, hvy_cl, hinty, _⟩ := EnvDenote.lookup_some hE hylk
      obtain ⟨nx, hvxn, _⟩ := hvx; subst hvxn
      obtain ⟨ny, hvyn, _⟩ := hvy; subst hvyn
      refine ⟨.iconst (nx + ny), ?_, ?_⟩
      · rw [Exp.substEnv_add]
        refine BigStep.add ?_ ?_
        · rw [Exp.substEnv_var_lookup x γ _ hlkx hvx_cl]; exact BigStep.iconst
        · rw [Exp.substEnv_var_lookup y γ _ hlky hvy_cl]; exact BigStep.iconst
      · refine ⟨nx + ny, rfl, ?_⟩
        simp [hintx nx rfl, hinty ny rfl]
  | @leq_var Γ x y r₁ r₂ hxlk hylk =>
      intro γ ρ hE
      obtain ⟨vx, hlkx, hvx, hvx_cl, hintx, _⟩ := EnvDenote.lookup_some hE hxlk
      obtain ⟨vy, hlky, hvy, hvy_cl, hinty, _⟩ := EnvDenote.lookup_some hE hylk
      obtain ⟨nx, hvxn, _⟩ := hvx; subst hvxn
      obtain ⟨ny, hvyn, _⟩ := hvy; subst hvyn
      refine ⟨.bconst (decide (nx ≤ ny)), ?_, ?_⟩
      · rw [Exp.substEnv_leq]
        refine BigStep.leq ?_ ?_
        · rw [Exp.substEnv_var_lookup x γ _ hlkx hvx_cl]; exact BigStep.iconst
        · rw [Exp.substEnv_var_lookup y γ _ hlky hvy_cl]; exact BigStep.iconst
      · refine ⟨decide (nx ≤ ny), rfl, ?_⟩
        simp [hintx nx rfl, hinty ny rfl]
  | @not_ Γ e r _ ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      obtain ⟨b, hvb, hp⟩ := hv; subst hvb
      refine ⟨.bconst (!b), ?_, ?_⟩
      · rw [Exp.substEnv_not]; exact BigStep.not_ hbs
      · exact ⟨!b, rfl, b, hp, rfl⟩
  | @and_ Γ e₁ e₂ r₁ r₂ _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v₁, hbs₁, hv₁⟩ := ih₁ hE
      obtain ⟨v₂, hbs₂, hv₂⟩ := ih₂ hE
      obtain ⟨b₁, hvb₁, hp₁⟩ := hv₁; subst hvb₁
      obtain ⟨b₂, hvb₂, hp₂⟩ := hv₂; subst hvb₂
      refine ⟨.bconst (b₁ && b₂), ?_, ?_⟩
      · rw [Exp.substEnv_and]; exact BigStep.and_ hbs₁ hbs₂
      · exact ⟨b₁ && b₂, rfl, b₁, b₂, hp₁, hp₂, rfl⟩
  | @ite Γ x e₁ e₂ r t hlk _ _ ih₁ ih₂ =>
      intro γ ρ hE
      obtain ⟨v, hlkγ, hv, _hcl, hint, hbool⟩ := EnvDenote.lookup_some hE hlk
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
          rw [Exp.substEnv_cons_lookup γ hlkγ (by simp [Val.closed, Val.fv])
                (EnvDenote.allClosed hE)] at hbs
          exact hbs
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
          rw [Exp.substEnv_cons_lookup γ hlkγ (by simp [Val.closed, Val.fv])
                (EnvDenote.allClosed hE)] at hbs
          exact hbs

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
