import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness (skeleton, κ-indexed)

  Algorithmic VC generation is sound w.r.t. the bidirectional and declarative
  typing rules. Every judgement is now parameterized by `κ : KEnv`.

  The headline theorems are stated and `sorry`-stubbed pending the full case
  analysis (deferred to Stage 13). The shape of the API is what
  `MakeHornUnderK.lean` consumes.
-/

/-! ## Sub soundness -/

theorem sub_sound (κ : KEnv) (Γ : TEnv) (s t : Ty) (c : Constraint) :
    sub s t = some c → Entail κ Γ (c κ) → Subtyp κ Γ s t := by
  intro hsub hent
  match s, t with
  | .refine .int r1, .refine .int r2 =>
    simp_all [sub]
    apply Subtyp.refine
    simp [Refinement.subImp, Formula.interp, Refinement.interp] at *
    intro ρ hm n hf
    have := hent ρ hm
    rw [←hsub] at this
    apply this
    assumption
  | .refine .bool r1, .refine .bool r2 =>
    simp_all [sub]
    apply Subtyp.refine
    simp [Refinement.subImp, Formula.interp, Refinement.interp] at *
    intro ρ hm
    have h := hent ρ hm ; rw [←hsub] at h
    obtain ⟨hl, hr⟩ := h
    and_intros
    · apply hl
    · apply hr
  | .arrow s1 t1, .arrow s2 t2 =>
    simp_all [sub]
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, sub s2 s1 = some c₁ := by grind
    obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub (t1.openVar 0 (EVar.fresh (s1.fv ++ (s2.fv ++ (t1.fv ++ t2.fv)))))
                                   (t2.openVar 0 (EVar.fresh (s1.fv ++ (s2.fv ++ (t1.fv ++ t2.fv))))) = some c₂ := by grind
    rw [hc₁, hc₂] at hsub ; simp at hsub
    apply Subtyp.arrow (x := EVar.fresh (s1.fv ++ (s2.fv ++ (t1.fv ++ t2.fv))))
    · have h := sub_sound κ Γ s2 s1 c₁ hc₁
      simp at h
      rw [←hsub] at hent
      exact h fun ρ hm => (hent ρ hm).1
    · apply EVar.fresh_not_mem
    · cases s2 with
      | refine b r => cases b with
        | int =>
          simp_all
          apply sub_sound _ _ _ _ c₂ hc₂
          intro ρ hm ; simp_all
          rw [←hsub] at hent
          have := (hent ρ hm.2).2 (ρ.ints _) hm.1
          simp_all
        | bool =>
          simp_all
          apply sub_sound _ _ _ _ c₂ hc₂
          intro ρ hm ; simp_all
          rw [←hsub] at hent
          have hb := (hent ρ hm.2).2
          by_cases h : ρ.bools (EVar.fresh (s1.fv ++ ((Ty.refine Base.bool r).fv ++ (t1.fv ++ t2.fv)))) = false
          · simp at h ; rw [h] at hm
            have := hb.1 hm.1
            have h' : (fun y => !decide (EVar.fresh (s1.fv ++ ((Ty.refine Base.bool r).fv ++ (t1.fv ++ t2.fv))) = y) && ρ.bools y) = ρ.bools := by
              funext ; grind
            rw [h'] at this ; simp_all
          · simp at h ; rw [h] at hm
            have := hb.2 hm.1
            have h' : (fun y => decide (EVar.fresh (s1.fv ++ ((Ty.refine Base.bool r).fv ++ (t1.fv ++ t2.fv))) = y) || ρ.bools y) = ρ.bools := by
              funext ; grind
            rw [h'] at this ; simp_all
      | arrow a1 a2 =>
        simp_all
        apply sub_sound _ _ _ _ c₂ hc₂
        intro ρ hm ; simp at hm
        rw [←hsub] at hent
        exact (hent ρ hm).2
  | .refine _ _ , .arrow _ _ | .arrow _ _, .refine _ _ | .refine .int _, .refine .bool _ | .refine .bool _, .refine .int _=>
    simp_all [sub]
  termination_by s.skel + t.skel

/-! ## Synth / Check soundness (mutual) -/

mutual
  theorem synth_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
      synth Γ e = some (c, t) → Entail κ Γ (c κ) → Synth κ Γ e t := by
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
    | .lam e | .letin e1 e2 | .and e1 e2 | .not e | .ite _ _ _  =>
      simp_all [synth]
    | .app e1 (.fvar y) =>
      simp_all [synth]
      obtain ⟨c1, s', t', hse⟩ : ∃ c s t, synth Γ e1 = some (c, .arrow s t) := by grind
      obtain ⟨c2, hy⟩ : ∃ c, check Γ (.fvar y) s' = some c := by grind
      simp_all
      rw [← hsynth.2]
      constructor <;>
      rw [←hsynth.1] at hent
      · exact synth_sound κ Γ e1 c1 _ hse fun ρ hm => (hent ρ hm).1
      · exact check_sound κ Γ (.fvar y) s' c2 hy fun ρ hm => (hent ρ hm).2
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
      check Γ e t = some c → Entail κ Γ (c κ) → Check κ Γ e t := by
    intro hcheck hent
    match e with
    | .bvar i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.bvar i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .fvar x =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.fvar x) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .iconst i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.iconst i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .bconst b =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.bconst b) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .add e1 e2 =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.add e1 e2) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
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
      apply Check.ite
      assumption
      apply check_sound _ _ _ _ _ hc₁
      intro ρ hm
      rw [←hcheck] at hent
      have := hent ρ hm.2
      simp_all
      by_cases h : (ρ.bools cn) = false
      · simp at h ; rw [h] at hm
        have := (hent ρ hm.2).1.1 hm.1
        have h' : (fun y => !decide (cn = y) && ρ.bools y) = ρ.bools := by grind
        rw [h'] at this ; simp_all
      · simp at h ; rw [h] at hm
        have := (hent ρ hm.2).1.2 hm.1
        have h' : (fun y => decide (cn = y) || ρ.bools y) = ρ.bools := by grind
        rw [h'] at this ; simp_all

      apply check_sound _ _ _ _ _ hc₂
      intro ρ hm
      rw [←hcheck] at hent
      have := hent ρ hm.2
      simp_all
      by_cases h : (ρ.bools cn) = false
      · simp at h ; rw [h] at hm
        have := (hent ρ hm.2).2.1 hm.1
        have h' : (fun y => !decide (cn = y) && ρ.bools y) = ρ.bools := by grind
        rw [h'] at this ; simp_all
      · simp at h ; rw [h] at hm
        have := (hent ρ hm.2).2.2 hm.1
        have h' : (fun y => decide (cn = y) || ρ.bools y) = ρ.bools := by grind
        rw [h'] at this ; simp_all
    | .lam e =>
      match t with
      | .refine _ r =>
        simp_all [check, synth]
      | .arrow s1 t1 =>
        simp_all [check]
        obtain ⟨c₁, hc₁⟩ : ∃ c₁, check ((EVar.fresh (TEnv.dom Γ ++ (e.fv ++ t1.fv)), s1) :: Γ)
            (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ t1.fv))) e)
            (Ty.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ t1.fv))) t1) = some c₁ := by grind
        simp_all
        apply Check.lam (x := EVar.fresh (Γ.dom ++ (e.fv ++ t1.fv)))
        apply EVar.fresh_not_mem
        apply check_sound _ _ _ _ _ hc₁
        intro ρ hm
        rw [←hcheck] at hent
        simp [implyBind] at hent
        match s1 with
        | .refine .int r =>
          have := hent ρ hm.2 (ρ.ints (EVar.fresh (Γ.dom ++ (e.fv ++ t1.fv)))) hm.1
          simp_all
        | .refine .bool r =>
          simp_all
          have := hent ρ hm.2
          by_cases h : (ρ.bools (EVar.fresh (Γ.dom ++ (e.fv ++ t1.fv)))) = false
          · simp at h ; rw [h] at hm
            have := hent ρ hm.2
            have h' : (fun y => !decide (EVar.fresh (Γ.dom ++ (e.fv ++ t1.fv)) = y) && ρ.bools y) = ρ.bools := by
              funext ; grind
            rw [h'] at this ; simp_all
          · simp at h ; rw [h] at hm
            have := this.2 hm.1
            have h' : (fun y => decide (EVar.fresh (Γ.dom ++ (e.fv ++ t1.fv)) = y) || ρ.bools y) = ρ.bools := by
              funext ; grind
            rw [h'] at this ; simp_all
        | .arrow s1' s2' =>
          simp_all
    | .letin e1 e2 =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ e1 = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, check ((EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv)), s) :: Γ)
          (Exp.openVar 0 (EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv))) e2) t = some c₂ := by grind
      simp_all
      rw [←hcheck] at hent
      apply Check.letin (x := EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv)))
      apply synth_sound _ _ _ _ _ hc₁
      intro ρ hm
      exact (hent ρ hm).1
      rw [List.append_assoc]
      apply EVar.fresh_not_mem
      apply check_sound _ _ _ _ _ hc₂
      intro ρ hm
      match s with
      | .refine .int r =>
        have := (hent ρ hm.2).2 (ρ.ints (EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv))))
        simp_all
      | .refine .bool r =>
        simp_all
        by_cases h : (ρ.bools (EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv)))) = false
        · simp at h ; rw [h] at hm
          have := (hent ρ hm.2).2.1 hm.1
          have h' : (fun y => !decide (EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv)) = y) && ρ.bools y) = ρ.bools := by grind
          simp_all
        · simp at h ; rw [h] at hm
          have := (hent ρ hm.2).2.2 hm.1
          have h' : (fun y => decide (EVar.fresh (Γ.dom ++ (e2.fv ++ t.fv)) = y) || ρ.bools y) = ρ.bools := by grind
          simp_all
      | .arrow s₁ s₂ =>
        simp_all
    | .leq (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ ((Exp.fvar x).leq (Exp.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .ann e t' =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ (.ann e t') = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .app e1 (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ (.app e1 (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | (.ite (.add _ _) _ _) | (.ite (.ite _ _ _) _ _) | (.ite (.leq _ _) _ _) | (.ite (.not _) _ _)
    | (.ite (.and _ _) _ _) | (.ite (.ann _ _) _ _) | (.ite (.app _ _) _ _) | (.ite (.letin _ _) _ _)
    | (.ite (.lam _) _ _) | (.ite (.bconst true) _ _) | (.ite (.bconst false) _ _)
    | (.ite (.iconst _) _ _) | (.ite (.bvar _) _ _) | (.not _) | (.and _ _)
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
  theorem synth_to_hastype {κ Γ e t} : Synth κ Γ e t → Hastype κ Γ e t := by
    intro h
    match h with
    | .var hl         => exact .var hl
    | .int_const      => exact .int_const
    | .bool_const     => exact .bool_const
    | .ann hck        => exact .ann (check_to_hastype hck)
    | .app hsy hck    => exact .app (synth_to_hastype hsy) (check_to_hastype hck)
    | .add_var hx hy  => exact .add_var hx hy
    | .leq_var hx hy  => exact .leq_var hx hy

  theorem check_to_hastype {κ Γ e t} : Check κ Γ e t → Hastype κ Γ e t := by
    intro h
    match h with
    | .sub hsy hsub        => exact .sub (synth_to_hastype hsy) hsub
    | .lam xf hck           => exact .lam xf (check_to_hastype hck)
    | .letin hsy xf hck     => exact .letin (synth_to_hastype hsy) xf (check_to_hastype hck)
    | .ite hlk hck1 hck2   =>
        exact .ite hlk (check_to_hastype hck1) (check_to_hastype hck2)
end

theorem synth_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
    synth Γ e = some (c, t) → Entail κ Γ (c κ) → Hastype κ Γ e t :=
  fun h hc => synth_to_hastype (synth_sound κ Γ e c t h hc)

theorem check_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint) :
    check Γ e t = some c → Entail κ Γ (c κ) → Hastype κ Γ e t :=
  fun h hc => check_to_hastype (check_sound κ Γ e t c h hc)

theorem topVC_decl_sound (κ : KEnv) (e : Exp) (t : Ty) :
    topVC κ [] e t → Hastype κ [] e t := by
  unfold topVC
  cases hck : check [] e t with
  | none   => intro hf; exact hf.elim
  | some c => intro h; exact check_decl_sound κ [] e t c hck (Entail.emp h)
