import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness (skeleton, κ-indexed)

  Algorithmic VC generation is sound w.r.t. the bidirectional and declarative
  typing rules. Every judgement is now parameterized by `κ : KEnv`.

-/

/-! ## Sub soundness -/

/-- `Exp.WFBVars` is preserved under `Exp.openVar`. (openVar replaces a `bvar k`
    with a `fvar x`, neither of which adds annotations or otherwise affects
    the WFBVars predicate.) -/
@[simp]
theorem Exp.WFBVars_openVar (e : Exp) (k : Nat) (x : EVar) :
    Exp.WFBVars (e.openVar k x) ↔ Exp.WFBVars e := by
  induction e generalizing k with
  | bvar _ => simp [Exp.openVar, Exp.WFBVars]; split <;> simp [Exp.WFBVars]
  | fvar _ | iconst _ | bconst _ => simp [Exp.openVar, Exp.WFBVars]
  | lam e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | letin e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | app e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | ann e t ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | and e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | not e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | leq e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₀, ih₁, ih₂]
  | add e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]


theorem sub_sound (κ : KEnv) (Γ : TEnv) (s t : Ty) (c : Constraint) :
    sub Γ s t = some c → CEntail κ Γ c → Subtyp κ Γ s t := by
  intro hsub hent
  match s, t with
  | .refine .int r1, .refine .int r2 =>
    simp only [sub, Option.some.injEq] at hsub
    subst hsub
    apply Subtyp.refine
    intro ρ hm
    simp only [Refinement.subImp, Formula.interp]
    exact hent ρ hm
  | .refine .bool r1, .refine .bool r2 =>
    simp only [sub, Option.some.injEq] at hsub
    subst hsub
    apply Subtyp.refine
    intro ρ hm
    simp only [Refinement.subImp, Formula.interp]
    exact hent ρ hm
  | .arrow s1 t1, .arrow s2 t2 =>
    simp_all [sub]
    -- use `set` so `w` stays opaque, preventing whnf blowup
    let w := (EVar.fresh
            (Γ.dom ++
              (Γ.tyFv ++
                (Γ.tyNamed ++
                  (s1.fv ++
                    (s2.fv ++
                      (t1.fv ++ (t2.fv ++ (s1.named ++ (s2.named ++ (t1.named ++ (t2.named ++ [nuName]))))))))))))
    have hwd : w = EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ
                          ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv
                          ++ Ty.named s1 ++ Ty.named s2
                          ++ Ty.named t1 ++ Ty.named t2 ++ [nuName]) := by grind
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, sub Γ s2 s1 = some c₁ := by
      rcases Option.eq_none_or_eq_some (sub Γ s2 s1) with eqn | eqs
      · simp_all
      · assumption
    obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub ((w, s2) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w) = some c₂ := by
      rcases Option.eq_none_or_eq_some (sub ((w, s2) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w)) with eqn | eqs
      · simp_all
      · assumption
    -- avoid `simp at hsub` to keep implyBind folded
    rw [hc₁, hc₂] at hsub
    simp only [Option.some.injEq] at hsub
    -- hsub : (fun ρ => c₁ ρ ∧ implyBind κ w s2 c₂ ρ) = c
    have hw : w ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ
                ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv
                ++ Ty.named s1 ++ Ty.named s2 ++ Ty.named t1 ++ Ty.named t2 ++ [nuName] := by
      grind [EVar.fresh_not_mem (Γ.dom ++
              (Γ.tyFv ++
                (Γ.tyNamed ++
                  (s1.fv ++
                    (s2.fv ++
                      (t1.fv ++ (t2.fv ++ (s1.named ++ (s2.named ++ (t1.named ++ (t2.named ++ [nuName])))))))))))]
    apply Subtyp.arrow (x := w) _ hw
    · apply sub_sound κ ((w, s2) :: Γ) _ _ c₂ hc₂
      intro ρ hm
      rw [←hsub] at hent
      simp only [List.mem_append, List.mem_singleton, not_or] at hw
      cases s2 with
      | refine b r =>
        have himply : Constraint.interp κ ρ (implyBind w (.refine b r) c₂) :=
          (hent ρ hm.2).2
        have hbr := (Constraint.interp_implyBind' κ r w c₂ ρ
                      (by grind) (by grind) (by grind)).mp himply
        have h := hbr (REnv.get b ρ w) hm.1
        rwa [REnv.update_self] at h
      | arrow _ _ => exact (hent ρ hm).2
    · apply sub_sound κ Γ s2 s1 c₁ hc₁
      intro ρ hm
      rw [←hsub] at hent
      exact (hent ρ hm).1
  | .refine _ _ , .arrow _ _ | .arrow _ _, .refine _ _ | .refine .int _, .refine .bool _ | .refine .bool _, .refine .int _=>
    simp_all [sub]
  termination_by s.skel + t.skel

/-! ## Synth / Check soundness (mutual) -/

mutual
  theorem synth_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
      synth Γ e = some (c, t) → CEntail κ Γ c → Synth κ Γ e t := by
    intro hsynth hent
    match e with
    | .bvar i =>
      simp_all [synth]
    | .fvar x =>
      simp_all [synth]
      rcases hsynth with ⟨t', ⟨hl, hc, hs⟩⟩
      match t' with
      | .refine .int r | .refine .bool r =>
        simp_all ; rw [←hs, ←self]
        constructor
        assumption
      | .arrow _ _ =>
        simp_all ; rw [←hs, ←self] ; rw [←hs] at hl
        constructor ; assumption
    | .iconst i | .bconst b =>
      simp_all [synth]
      rw [←hsynth.2]
      constructor
    | .not (.fvar x) =>
      simp_all [synth]
      obtain ⟨r, hr⟩ : ∃ r, List.lookup x Γ = some (.refine .bool r) := by grind
      simp_all ; rw [←hsynth.2] ; constructor ; assumption
    | .and (.fvar x) (.fvar y) =>
      simp_all [synth]
      obtain ⟨rx, ry, hrx, hry⟩ : ∃ rx ry,
          List.lookup x Γ = some (.refine .bool rx) ∧
          List.lookup y Γ = some (.refine .bool ry) := by grind
      simp_all ; rw [←hsynth.2] ; constructor <;> assumption
    | .lam e | .letin e1 e2 | .ite _ _ _  =>
      simp_all [synth]
    | .app e1 (.fvar y) =>
      simp_all [synth]
      obtain ⟨c1, s', t', hse⟩ : ∃ c s t, synth Γ e1 = some (c, .arrow s t) := by grind
      obtain ⟨c2, hy⟩ : ∃ c, check Γ (.fvar y) s' = some c := by grind
      simp_all
      obtain ⟨⟨hyfv, hyn, hyν⟩, hceq, hteq⟩ := hsynth
      rw [← hteq]
      rw [← hceq] at hent
      exact Synth.app
        (synth_sound κ Γ e1 c1 _ hse fun ρ hm => (hent ρ hm).1)
        (check_sound κ Γ (.fvar y) s' c2 hy fun ρ hm => (hent ρ hm).2)
        hyfv hyn hyν
    | .ann e1 t' =>
      simp_all [synth]
      obtain ⟨c', hc⟩ : ∃ c, check Γ e1 t' = some c := by grind
      simp_all
      exact Synth.ann (check_sound κ Γ e1 t c hc hent)
    | .leq (.fvar x) (.fvar y) | .add (.fvar x) (.fvar y) =>
      simp_all [synth]
      obtain ⟨a, b, ha, hb⟩ : ∃ a b, List.lookup x Γ = some (.refine .int a) ∧
          List.lookup y Γ = some (.refine .int b) := by grind
      simp_all
      rw [←hsynth.2]
      constructor <;> assumption
    | (.not (.add _ _)) | (.not (.ite _ _ _)) | (.not (.leq _ _)) | (.not (.not _))
    | (.not (.and _ _)) | (.not (.ann _ _)) | (.not (.app _ _)) | (.not (.letin _ _))
    | (.not (.lam _)) | (.not (.bconst _)) | (.not (.iconst _)) | (.not (.bvar _))
    | (.and (.add _ _) _) | (.and (.ite _ _ _) _) | (.and (.leq _ _) _) | (.and (.not _) _)
    | (.and (.and _ _) _) | (.and (.ann _ _) _) | (.and (.app _ _) _) | (.and (.letin _ _) _)
    | (.and (.lam _) _) | (.and (.bconst _) _) | (.and (.iconst _) _) | (.and (.bvar _) _)
    | (.and (.fvar _) (.add _ _)) | (.and (.fvar _) (.ite _ _ _)) | (.and (.fvar _) (.leq _ _))
    | (.and (.fvar _) (.not _)) | (.and (.fvar _) (.and _ _)) | (.and (.fvar _) (.ann _ _))
    | (.and (.fvar _) (.app _ _)) | (.and (.fvar _) (.letin _ _)) | (.and (.fvar _) (.lam _))
    | (.and (.fvar _) (.bconst _)) | (.and (.fvar _) (.iconst _)) | (.and (.fvar _) (.bvar _))
    | (.add (.add _ _) _) | (.add (.leq _ _) _) | (.add (.and _ _) _) | (.add (.ann _ _) _) | (.add (.app _ _) _)
    | (.add (.ite _ _ _) _) | (.add (.not _) _) | (.add (.letin _ _) _) | (.add (.lam _) _) | (.add (.bconst _) _)
    | (.add (.iconst _) _) | (.add (.fvar _) (.add _ _)) | (.add (.fvar _) (.ite _ _ _)) | (.add (.fvar _) (.leq _ _))
    | (.add (.fvar _) (.not _)) | (.add (.fvar _) (.and _ _)) | (.add (.fvar _) (.ann _ _)) | (.add (.fvar _) (.app _ _))
    | (.add (.fvar _) (.letin _ _)) | (.add (.fvar _) (.lam _)) | (.add (.fvar _) (.bconst _)) | (.add (.fvar _) (.iconst _))
    | (.add (.fvar _) (.bvar _)) | (.add (.bvar _) _) | (.leq (.add _ _) _) | (.leq (.ite _ _ _) _) | (.leq (.leq _ _) _)
    | (.leq (.not _) _) | (.leq (.and _ _) _) | (.leq (.ann _ _) _) | (.leq (.app _ _) _) | (.leq (.letin _ _) _) | (.leq (.lam _) _)
    | (.leq (.bconst _) _) | (.leq (.iconst _) _) | (.leq (.fvar _) (.add _ _)) | (.leq (.fvar _) (.ite _ _ _)) | (.leq (.fvar _) (.leq _ _))
    | (.leq (.fvar _) (.not _)) | (.leq (.fvar _) (.and _ _)) | (.leq (.fvar _) (.ann _ _)) | (.leq (.fvar _) (.app _ _))
    | (.leq (.fvar _) (.letin _ _)) | (.leq (.fvar _) (.lam _)) | (.leq (.fvar _) (.bconst _)) | (.leq (.fvar _) (.iconst _))
    | (.leq (.fvar _) (.bvar _)) | (.leq (.bvar _) _) | (.app _ (.add _ _)) | (.app _ (.ite _ _ _)) | (.app _ (.leq _ _)) | (.app _ (.not _))
    | (.app _ (.and _ _)) | (.app _ (.ann _ _)) | (.app _ (.app _ _)) | (.app _ (.letin _ _)) | (.app _ (.lam _)) | (.app _ (.bconst _))
    | (.app _ (.iconst _)) | (.app _ (.bvar _))
      => simp_all [synth]
  termination_by 2*e.skel

  theorem check_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint) :
      check Γ e t = some c → CEntail κ Γ c → Check κ Γ e t := by
    intro hcheck hent
    match e with
    | .bvar i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.bvar i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .fvar x =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.fvar x) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .iconst i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.iconst i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .bconst b =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.bconst b) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .add e1 e2 =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.add e1 e2) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .ite (.fvar cn) bt bf =>
      simp_all [check]
      obtain ⟨r, hr⟩ : ∃ r, List.lookup cn Γ = some (.refine .bool r) := by grind
      simp_all
      obtain ⟨c₁, c₂, hc₁, hc₂⟩ : ∃ c₁ c₂,
          (check ((cn, Ty.refine Base.bool { fmla := r.fmla.and (Formula.eqB (Term.fvar Base.bool nuName) (Term.const Base.bool true)) }) :: Γ) bt t = some c₁) ∧
          (check ((cn, Ty.refine Base.bool { fmla := r.fmla.and (Formula.eqB (Term.fvar Base.bool nuName) (Term.const Base.bool false)) }) :: Γ) bf t = some c₂) := by
        grind
      simp_all
      -- Recover the exact constraint produced for the `ite`.
      have hcnν : cn ≠ nuName := by grind [check]
      have hcval : c = .conj (.impl (.eqB (.fvar .bool cn) (.const .bool true))  c₁)
                            (.impl (.eqB (.fvar .bool cn) (.const .bool false)) c₂) := by
        grind [check]
      subst hcval
      apply Check.ite hr hcnν
      · -- then-branch: cn = true ⇒ c₁  (cn already bound in ρ)
        apply check_sound _ _ _ _ _ hc₁
        intro ρ hm
        refine (hent ρ hm.2).1 ?_
        have hb : ρ.bools cn = true := by
          have h := hm.1
          simp only [Refinement.interp, Formula.interp, Term.interp, REnv.get,
                     REnv.update] at h
          grind
        simpa [Formula.interp, Term.interp, REnv.get] using hb
      · -- else-branch: cn = false ⇒ c₂
        apply check_sound _ _ _ _ _ hc₂
        intro ρ hm
        refine (hent ρ hm.2).2 ?_
        have hb : ρ.bools cn = false := by
          have h := hm.1
          simp only [Refinement.interp, Formula.interp, Term.interp, REnv.get,
                     REnv.update] at h
          grind
        simpa [Formula.interp, Term.interp, REnv.get] using hb
    | .lam e =>
      match t with
      | .refine _ r =>
        simp_all [check, synth]
      | .arrow s1 t1 =>
        simp_all [check]
        -- Use the LITERAL right-associated fresh expression (matches simp's normal form
        -- so the second simp_all can substitute hc₁ into hcheck).
        obtain ⟨c₁, hc₁⟩ : ∃ c₁, check ((EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++
                                              (Ty.named s1 ++ (Ty.named t1 ++
                                              (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName]))))))))
                                            , s1) :: Γ)
            (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++
                                              (Ty.named s1 ++ (Ty.named t1 ++
                                              (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName])))))))))
                                            e)
            (Ty.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++
                                              (Ty.named s1 ++ (Ty.named t1 ++
                                              (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName])))))))))
                                            t1) = some c₁ := by grind
        simp_all
        let L₀ : List EVar := TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++
                              (Ty.named s1 ++ (Ty.named t1 ++
                              (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName])))))))
        let x₀ : EVar := EVar.fresh L₀
        -- 1. Body proof at the specific fresh witness `x₀`.
        have hbody₀ :
            Check κ ((x₀, s1) :: Γ) (Exp.openVar 0 x₀ e) (Ty.openVar 0 x₀ t1) := by
          apply check_sound κ _ _ _ _ hc₁
          intro ρ hmρ
          have hΓρ : ModelsEnv κ ρ Γ := by
            cases s1 with
            | refine _ _ => exact hmρ.2
            | arrow _ _  => exact hmρ
          have hcρ := hent ρ hΓρ
          rw [← hcheck] at hcρ
          have hfr : x₀ ∉ L₀ := EVar.fresh_not_mem L₀
          simp only [L₀, List.mem_append, List.mem_singleton, not_or] at hfr
          cases s1 with
          | refine b r =>
            have hbr := (Constraint.interp_implyBind' κ r x₀ c₁ ρ
                          (by grind) (by grind) (by grind)).mp hcρ
            have h := hbr (REnv.get b ρ x₀) hmρ.1
            rwa [REnv.update_self] at h
          | arrow _ _ => exact hcρ
        have hfresh₀ : x₀ ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++
                       e.fv ++ s1.fv ++ t1.fv ++ Ty.named s1 ++ Ty.named t1 ++ [nuName] := by
          have h := EVar.fresh_not_mem L₀
          simp only [L₀, List.mem_append, List.mem_singleton, not_or] at h ⊢
          grind
        exact Check.lam hfresh₀ hbody₀
    | .letin e1 e2 =>
      -- check Γ (.letin e1 e2) t algorithm: synth e1 → (c₁, s); check ((x₀, s) :: Γ) (e2.openVar 0 x₀) t = some c₂
      simp_all [check]
      obtain ⟨c₁, s, hsynth⟩ : ∃ c₁ s, synth Γ e1 = some (c₁, s) := by grind
      -- Use LITERAL right-associated fresh expression (matches simp's normal form).
      obtain ⟨c₂, hcheck₂⟩ : ∃ c₂, check ((EVar.fresh (TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++
                                              (Ty.named s ++ (Ty.named t ++
                                              (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName]))))))))
                                            , s) :: Γ)
          (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++
                                              (Ty.named s ++ (Ty.named t ++
                                              (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName])))))))))
                                            e2) t = some c₂ := by grind
      simp_all
      let L₀ : List EVar := TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++
                             (Ty.named s ++ (Ty.named t ++
                             (TEnv.tyFv Γ ++ (TEnv.tyNamed Γ ++ [nuName])))))))
      let x₀ : EVar := EVar.fresh L₀
      -- 1. Synth at e1 via synth_sound.
      have hsy : Synth κ Γ e1 s := by
        apply synth_sound _ _ _ _ _ hsynth
        intro ρ hρ
        have := hent ρ hρ
        rw [←hcheck] at this
        exact this.1
      -- 2. Body Check at x₀ via check_sound.
      have hbody₀ : Check κ ((x₀, s) :: Γ) (Exp.openVar 0 x₀ e2) t := by
        apply check_sound _ _ _ _ _ hcheck₂
        intro ρ hmρ
        have hΓρ : ModelsEnv κ ρ Γ := by
          cases s with
          | refine _ _ => exact hmρ.2
          | arrow _ _  => exact hmρ
        have hcρ := hent ρ hΓρ
        rw [← hcheck] at hcρ
        have himply : Constraint.interp κ ρ (implyBind x₀ s c₂) := hcρ.2
        have hfr : x₀ ∉ L₀ := EVar.fresh_not_mem L₀
        simp only [L₀, List.mem_append, List.mem_singleton, not_or] at hfr
        cases s with
        | refine b r =>
          have hbr := (Constraint.interp_implyBind' κ r x₀ c₂ ρ
                        (by grind) (by grind) (by grind)).mp himply
          have h := hbr (REnv.get b ρ x₀) hmρ.1
          rwa [REnv.update_self] at h
        | arrow _ _ => exact himply
      have hfresh₀ : x₀ ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++
                     e2.fv ++ s.fv ++ t.fv ++ Ty.named s ++ Ty.named t ++ [nuName] := by
        have h := EVar.fresh_not_mem L₀
        simp only [L₀, List.mem_append, List.mem_singleton, not_or] at h ⊢
        grind
      exact Check.letin hsy hfresh₀ hbody₀
      -- have hx₀_fresh : x₀ ∉ Γ.dom ++ s.fv ++ e2.fv ++ Ty.fv t
      --         ++ Ty.named s ++ Ty.named t
      --         ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName] := by
      --   have hx₀_fresh_L₀ : x₀ ∉ L₀ := EVar.fresh_not_mem _
      --   grind
      -- exact Check.rename_letin_body x₀ x hx₀_fresh hx_fresh hbody₀
    | .leq (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ ((Exp.fvar x).leq (Exp.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .ann e t' =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ (.ann e t') = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .app e1 (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ (.app e1 (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .not (.fvar x) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.not (.fvar x)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .and (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.and (.fvar x) (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | (.ite (.add _ _) _ _) | (.ite (.ite _ _ _) _ _) | (.ite (.leq _ _) _ _) | (.ite (.not _) _ _)
    | (.ite (.and _ _) _ _) | (.ite (.ann _ _) _ _) | (.ite (.app _ _) _ _) | (.ite (.letin _ _) _ _)
    | (.ite (.lam _) _ _) | (.ite (.bconst true) _ _) | (.ite (.bconst false) _ _)
    | (.ite (.iconst _) _ _) | (.ite (.bvar _) _ _)
    | (.not (.bvar _)) | (.not (.iconst _)) | (.not (.bconst _)) | (.not (.lam _))
    | (.not (.letin _ _)) | (.not (.app _ _)) | (.not (.ann _ _)) | (.not (.and _ _))
    | (.not (.add _ _)) | (.not (.leq _ _)) | (.not (.ite _ _ _)) | (.not (.not _))
    | (.and (.fvar _) (.bvar _)) | (.and (.fvar _) (.iconst _)) | (.and (.fvar _) (.bconst _))
    | (.and (.fvar _) (.lam _)) | (.and (.fvar _) (.letin _ _)) | (.and (.fvar _) (.app _ _))
    | (.and (.fvar _) (.ann _ _)) | (.and (.fvar _) (.and _ _)) | (.and (.fvar _) (.add _ _))
    | (.and (.fvar _) (.leq _ _)) | (.and (.fvar _) (.ite _ _ _)) | (.and (.fvar _) (.not _))
    | (.and (.bvar _) _) | (.and (.iconst _) _) | (.and (.bconst _) _) | (.and (.lam _) _)
    | (.and (.letin _ _) _) | (.and (.app _ _) _) | (.and (.ann _ _) _)
    | (.and (.add _ _) _) | (.and (.leq _ _) _) | (.and (.ite _ _ _) _) | (.and (.not _) _) | (.and (.and _ _) _)
    | (.leq (.add _ _) _) | (.leq (.ite _ _ _) _) | (.leq (.leq _ _) _) | (.leq (.not _) _)
    | (.leq (.and _ _) _) | (.leq (.ann _ _) _) | (.leq (.app _ _) _) | (.leq (.letin _ _) _)
    | (.leq (.lam _) _) | (.leq (.bconst _) _) | (.leq (.iconst _) _) | (.leq (.fvar _) (.add _ _))
    | (.leq (.fvar _) (.ite _ _ _)) | (.leq (.fvar _) (.leq _ _)) | (.leq (.fvar _) (.not _)) | (.leq (.fvar _) (.and _ _))
    | (.leq (.fvar _) (.ann _ _)) | (.leq (.fvar _) (.app _ _)) | (.leq (.fvar _) (.letin _ _)) | (.leq (.fvar _) (.lam _))
    | (.leq (.fvar _) (.bconst _)) | (.leq (.fvar _) (.iconst _)) | (.leq (.fvar _) (.bvar _)) | (.leq (.bvar _) _)
    | (.app _ (.add _ _)) | (.app _ (.ite _ _ _)) | (.app _ (.leq _ _)) | (.app _ (.not _))
    | (.app _ (.and _ _)) | (.app _ (.ann _ _)) | (.app _ (.app _ _)) | (.app _ (.letin _ _)) | (.app _ (.lam _)) | (.app _ (.bconst _))
    | (.app _ (.iconst _)) | (.app _ (.bvar _))=>
      simp_all [check, synth]
  termination_by 2 * e.skel + 1
end

/-! ## Bidirectional → declarative -/

mutual
  theorem synth_to_hastype {κ Γ e t}
      (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (h : Synth κ Γ e t) :
      Hastype κ Γ e t ∧ Ty.WFBVars t := by
    match h with
    | .var hl =>
      have htw := hΓ.lookup hl
      exact ⟨.var hl htw, Ty.WFBVars_self _ _ htw⟩
    | .int_const => exact ⟨.int_const, Ty.WFBVars_prim _⟩
    | .bool_const => exact ⟨.bool_const, Ty.WFBVars_primBool _⟩
    | .ann hck =>
      simp only [Exp.WFBVars] at hE
      have htw := hE.1
      have hht := check_to_hastype hΓ hE.2 htw hck
      exact ⟨.ann hht htw, htw⟩
    | .app hsy hck hyfv hyn hyν =>
      simp only [Exp.WFBVars] at hE
      have ⟨hht1, htw_arr⟩ := synth_to_hastype hΓ hE.1 hsy
      have htw_s_t := htw_arr
      simp only [Ty.WFBVars, Ty.WFBVarCtx] at htw_s_t
      have hht2 := check_to_hastype hΓ (by simp [Exp.WFBVars]) htw_s_t.1 hck
      refine ⟨.app hht1 hht2 hyfv hyn hyν, ?_⟩
      exact Ty.WFBVarCtx_openVar_last _ [] _ _ htw_s_t.2
    | .add_var hxlk hylk =>
      have hxν := hΓ.lookup_ne_nu hxlk
      have hyν := hΓ.lookup_ne_nu hylk
      exact ⟨.add_var hxlk hylk hxν hyν, Ty.WFBVars_add_result _ _⟩
    | .leq_var hxlk hylk =>
      have hxν := hΓ.lookup_ne_nu hxlk
      have hyν := hΓ.lookup_ne_nu hylk
      exact ⟨.leq_var hxlk hylk hxν hyν, Ty.WFBVars_leq_result _ _⟩
    | .not_var hxlk =>
      have hxν := hΓ.lookup_ne_nu hxlk
      exact ⟨.not_var hxlk hxν, Ty.WFBVars_not_result _⟩
    | .and_var hxlk hylk =>
      have hxν := hΓ.lookup_ne_nu hxlk
      have hyν := hΓ.lookup_ne_nu hylk
      exact ⟨.and_var hxlk hylk hxν hyν, Ty.WFBVars_and_result _ _⟩

  theorem check_to_hastype {κ Γ e t}
      (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t)
      (h : Check κ Γ e t) :
      Hastype κ Γ e t := by
    match h with
    | .sub hsy hsub =>
      have ⟨hht, _⟩ := synth_to_hastype hΓ hE hsy
      exact .sub hht hsub ht
    | .lam hfresh hck =>
      rename_i e s₁ s₂ x
      have hxν : x ≠ nuName := by
        have h := hfresh
        simp only [List.mem_append, List.mem_singleton, not_or] at h
        exact h.2
      have ht_split : Ty.WFBVarCtx [] s₁ ∧ Ty.WFBVarCtx [s₁.optBase] s₂ := by
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at ht; exact ht
      have hs₂_open_wfb : Ty.WFBVars (s₂.openVar 0 x) :=
        Ty.WFBVarCtx_openVar_last s₂ [] s₁.optBase x ht_split.2
      have hΓ_ext : TEnv.WFBVars ((x, s₁) :: Γ) := hΓ.cons ht_split.1 hxν
      have hE_ext : Exp.WFBVars (e.openVar 0 x) := by
        simp only [Exp.WFBVars] at hE; exact (Exp.WFBVars_openVar e 0 x).mpr hE
      exact .lam ht hfresh (check_to_hastype hΓ_ext hE_ext hs₂_open_wfb hck)
    | .letin hsy hfresh hck =>
      rename_i e₁ e₂ s x
      simp only [Exp.WFBVars] at hE
      have ⟨hht1, hs_wfb⟩ := synth_to_hastype hΓ hE.1 hsy
      have hxν : x ≠ nuName := by
        have h := hfresh
        simp only [List.mem_append, List.mem_singleton, not_or] at h
        exact h.2
      have hΓ_ext : TEnv.WFBVars ((x, s) :: Γ) := hΓ.cons hs_wfb hxν
      have hE_ext : Exp.WFBVars (e₂.openVar 0 x) :=
        (Exp.WFBVars_openVar e₂ 0 x).mpr hE.2
      exact .letin ht hht1 hfresh (check_to_hastype hΓ_ext hE_ext ht hck)
    | .ite hlk hxν hck1 hck2 =>
      rename_i x e₁ e₂ r
      simp only [Exp.WFBVars] at hE
      obtain ⟨_, hE1, hE2⟩ := hE
      -- Get WFBVars of the original (x, .refine .bool r) binding.
      have hr_wfb : Ty.WFBVars (.refine .bool r) := hΓ.lookup hlk
      -- The strengthened refinement is WFBVars: `r.fmla.and (.eqB ν const)` has no
      -- bvars at any level (r.fmla has none by hr_wfb; the conjunct has only fvars
      -- and consts).
      have hstr_wfb : ∀ (const : Bool), Ty.WFBVars (.refine .bool
          ⟨.and r.fmla (.eqB (.fvar .bool nuName) (.const .bool const))⟩) := by
        intro const
        simp only [Ty.WFBVars, Ty.WFBVarCtx, Formula.hasBVar, Term.hasBVar]
        intro b k hbv
        -- hbv : Formula.hasBVar b k r.fmla ∨ False ∨ False
        simp only [or_false] at hbv
        -- hbv : Formula.hasBVar b k r.fmla
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at hr_wfb
        exact hr_wfb b k hbv
      -- Extended TEnv.WFBVars for true / false branches.
      have hΓ1 : TEnv.WFBVars ((x, .refine .bool
          ⟨.and r.fmla (.eqB (.fvar .bool nuName) (.const .bool true))⟩) :: Γ) :=
        hΓ.cons (hstr_wfb true) hxν
      have hΓ2 : TEnv.WFBVars ((x, .refine .bool
          ⟨.and r.fmla (.eqB (.fvar .bool nuName) (.const .bool false))⟩) :: Γ) :=
        hΓ.cons (hstr_wfb false) hxν
      have hht1 := check_to_hastype hΓ1 hE1 ht hck1
      have hht2 := check_to_hastype hΓ2 hE2 ht hck2
      exact .ite hlk hxν ht hht1 hht2
end

theorem synth_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) :
    synth Γ e = some (c, t) → CEntail κ Γ c → Hastype κ Γ e t :=
  fun h hc => (synth_to_hastype hΓ hE (synth_sound κ Γ e c t h hc)).1

theorem check_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    check Γ e t = some c → CEntail κ Γ c → Hastype κ Γ e t :=
  fun h hc => check_to_hastype hΓ hE ht (check_sound κ Γ e t c h hc)

theorem topVC_decl_sound (κ : KEnv) (e : Exp) (t : Ty)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    topVC κ [] e t → Hastype κ [] e t := by
  unfold topVC
  cases hck : check [] e t with
  | none   => intro hf; exact hf.elim
  | some c =>
    intro h
    have hΓ_nil : TEnv.WFBVars [] := by
      refine ⟨?_, ?_⟩
      · intro x s hmem; simp at hmem
      · simp [TEnv.dom]
    exact check_decl_sound κ [] e t c hΓ_nil hE ht hck (fun ρ _ => h ρ)
