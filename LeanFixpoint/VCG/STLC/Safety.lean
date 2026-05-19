import LeanFixpoint.VCG.STLC.Semantics
import LeanFixpoint.VCG.STLC.Declarative
import LeanFixpoint.VCG.STLC.Soundness

open STLC

/-! # Refinement Type Safety for STLC (LN + deep refinements + κ)

  We prove four headline results:

    (T1) `subtyp_sound`         — Subtyping is semantic inclusion of denotations.
    (T2) `hastype_fundamental`  — Well-typed terms evaluate to values in their
                                   denotation, under a closing value substitution.
    (T3) `type_safety`          — Closed-term safety (corollary of T2).
    (T4) `vcgen_safety`         — End-to-end VCGen safety:
                                   `topVC κ [] e t → ∃ v, e ⇓ v ∧ ⟦t⟧κ ρ_∅ v`.

  All four are κ-indexed and operate over the new locally-nameless syntax with
  deep `Formula` refinements. The arrow case of the logical relation is stated
  in the canonical cofinite form (`∃ L, ∀ x ∉ L, …`), with the rename keystone
  (`TyDenote.rename`) proved as a separate lemma.

  This file is the **Stage A** skeleton — definitions and theorem statements are
  final; proofs are top-level `sorry`. Subsequent stages (LN helpers in
  Substitution.lean, then `TyDenote.rename`, then T1, then T2 case-by-case)
  fill these in.
-/

namespace STLC

/-- Extend `ρ` at name `x` with a base value extracted from `va`, where the
    base is determined by `s`. For an arrow-typed `s` (or any val/type mismatch)
    the update is a no-op — `t.openVar 0 x` cannot reference an arrow-typed
    binder via `REnv` slots. -/
@[simp]
def REnv.extendBy : Ty → REnv → EVar → Val → REnv
  | .refine .int  _, ρ, x, .iconst n => ρ.update .int  x n
  | .refine .bool _, ρ, x, .bconst b => ρ.update .bool x b
  | _, ρ, _, _ => ρ

end STLC

/-! ## Logical relation: ⟦τ⟧ as a predicate on values, κ-indexed and parameterized by ρ.

  - **Refinement bases**: `v` is `.iconst n` / `.bconst b` and the deep refinement
    holds at that value under the supplied κ-assignment.
  - **Arrow**: `v` is a locally-closed closure (`.clos body` with body `lc_at 1`),
    and *for some cofinite set* `L` of names, every fresh `x ∉ L` works as an
    opener for the codomain. The cofinite shape is the canonical LN logical
    relation form (cf. Charguéraud's POPLMark-Reloaded notes) — it gives the
    consumers of the LR (`subtyp_sound`/`hastype_fundamental`) the freedom to
    pick whichever name they need via the `TyDenote.rename` lemma.

  Termination: structural by `Ty.skel`. Both recursive positions on the arrow
  case (`s` and `t.openVar 0 x`) decrease via `Ty.skel_openVar`. -/
def TyDenote : KEnv → Ty → REnv → Val → Prop
  | κ, .refine .int  r, ρ, v => ∃ n : Int,  v = .iconst n ∧ Refinement.interp κ r ρ n
  | κ, .refine .bool r, ρ, v => ∃ b : Bool, v = .bconst b ∧ Refinement.interp κ r ρ b
  | κ, .arrow s t,      ρ, v =>
      ∃ body, v = .clos body ∧
        Val.lc (.clos body) ∧ Val.closed (.clos body) ∧
        ∃ L : List EVar, ∀ x, x ∉ L →
          ∀ va, TyDenote κ s ρ va →
            ∃ vr, BigStep (body.openVal 0 va) vr ∧
                  TyDenote κ (t.openVar 0 x) (REnv.extendBy s ρ x va) vr
termination_by _ t _ _ => t.skel
decreasing_by all_goals (simp_wf; omega)

/-- Every value in the denotation is closed (no free names). The refinement
    cases follow from `Val.fv` of `iconst`/`bconst` being empty; the arrow
    case is required by the LR definition. -/
theorem TyDenote.closed {κ : KEnv} {t : Ty} {ρ : REnv} {v : Val}
    (h : TyDenote κ t ρ v) : Val.closed v := by
  cases t with
  | refine b r =>
    cases b with
    | int  =>
      simp only [TyDenote] at h
      obtain ⟨n, hvn, _⟩ := h
      subst hvn; simp [Val.closed, Val.fv]
    | bool =>
      simp only [TyDenote] at h
      obtain ⟨bv, hvb, _⟩ := h
      subst hvb; simp [Val.closed, Val.fv]
  | arrow s t =>
    simp only [TyDenote] at h
    obtain ⟨_, hvc, _, hcl, _⟩ := h
    subst hvc
    exact hcl

/-! ## Closing-substitution agreement

  `EnvAgrees κ Γ γ ρ` says: `γ` (a value-substitution list) provides a value
  in the LR of each Γ-binding, and `ρ` reflects `γ` on the `Int`/`Bool` slots
  for base-typed bindings (so `var` can recover the slot witness).

  Mirrors the old `EnvDenote` but is now orthogonal to `TyDenote` (no inlined
  arrow-LR machinery). Duplicate keys are tolerated (head-shadowed entries from
  `ite`'s strengthened context). -/
def EnvAgrees : KEnv → TEnv → List (EVar × Val) → REnv → Prop
  | _, [],            [],            _ => True
  | κ, (x, t) :: Γ,   (y, v) :: γ,   ρ =>
        x = y ∧
        EnvAgrees κ Γ γ ρ ∧
        TyDenote κ t ρ v ∧
        (∀ n, v = .iconst n → ρ.ints  x = n) ∧
        (∀ b, v = .bconst b → ρ.bools x = b)
  | _, _, _, _ => False

/-- `EnvAgrees` implies pointwise closedness of `γ`. -/
theorem EnvAgrees.allClosed :
    ∀ {κ Γ γ ρ}, EnvAgrees κ Γ γ ρ → Subst.AllVClosed γ
  | _, [],            [],          _, _ => True.intro
  | _, (_, _) :: _,   (_, v) :: γ, _, h => by
      obtain ⟨_, hΓ, hv, _, _⟩ := h
      exact ⟨TyDenote.closed hv, EnvAgrees.allClosed hΓ⟩
  | _, [],            _ :: _,      _, h => by cases h
  | _, _ :: _,        [],          _, h => by cases h

/-- `EnvAgrees` projects to `ModelsEnv`: each refined Γ-binding's refinement
    holds at the ρ-slot value, derived from the value sitting in `γ`. -/
theorem EnvAgrees.toModelsEnv :
    ∀ {κ Γ γ ρ}, EnvAgrees κ Γ γ ρ → ModelsEnv κ ρ Γ
  | _, [],                          [],          _, _ => by simp [ModelsEnv]
  | _, (x, .refine b r) :: Γ,       (_, v) :: _, ρ, h => by
      obtain ⟨_, hΓ, hv, hint, hbool⟩ := h
      refine ⟨?_, EnvAgrees.toModelsEnv hΓ⟩
      cases b with
      | int  =>
        simp only [TyDenote] at hv
        obtain ⟨n, hvn, hp⟩ := hv
        have hρ : ρ.ints x = n := hint n hvn
        simp [REnv.get, hρ]; exact hp
      | bool =>
        simp only [TyDenote] at hv
        obtain ⟨bv, hvb, hp⟩ := hv
        have hρ : ρ.bools x = bv := hbool bv hvb
        simp [REnv.get, hρ]; exact hp
  | _, (_, .arrow _ _) :: _,        (_, _) :: _, _, h => by
      obtain ⟨_, hΓ, _, _, _⟩ := h
      simp [ModelsEnv]; exact EnvAgrees.toModelsEnv hΓ
  | _, [],                          _ :: _,      _, h => by cases h
  | _, _ :: _,                      [],          _, h => by cases h

/-- Looking up `x` in Γ produces a corresponding value in `γ` matching its
    type, along with the closedness and ρ-slot witnesses. -/
theorem EnvAgrees.lookup_some :
    ∀ {κ Γ γ ρ}, EnvAgrees κ Γ γ ρ →
    ∀ {x t}, Γ.lookup x = some t →
    ∃ v, Subst.lookup x γ = some v ∧ TyDenote κ t ρ v ∧ Val.closed v ∧
         (∀ n, v = .iconst n → ρ.ints  x = n) ∧
         (∀ b, v = .bconst b → ρ.bools x = b)
  | _, [],          [],          _, _, _, _, hl => by simp [List.lookup] at hl
  | _, (y, _) :: _, (_, v) :: γ, ρ, h, x, t, hl => by
      obtain ⟨hxy, hΓ, hv, hint, hbool⟩ := h
      subst hxy
      by_cases heq : x = y
      · subst heq
        simp [List.lookup] at hl
        subst hl
        refine ⟨v, ?_, hv, TyDenote.closed hv, hint, hbool⟩
        show (if x = x then some v else Subst.lookup x γ) = some v
        rw [if_pos rfl]
      · have hne_beq : (x == y) = false := by
          rw [beq_eq_false_iff_ne]; exact heq
        simp only [List.lookup, hne_beq] at hl
        obtain ⟨v', hlk, hd, hcl, hi, hb⟩ := EnvAgrees.lookup_some hΓ hl
        refine ⟨v', ?_, hd, hcl, hi, hb⟩
        show (if x = y then some v else Subst.lookup x γ) = some v'
        rw [if_neg heq]
        exact hlk
  | _, [],          _ :: _,      _, h, _, _, _ => by cases h
  | _, _ :: _,      [],          _, h, _, _, _ => by cases h

/-! ## T1 — Subtyping is semantic inclusion of denotations -/

theorem subtyp_sound {κ Γ s t} (hsub : Subtyp κ Γ s t) :
    ∀ {ρ}, ModelsEnv κ ρ Γ → ∀ {v}, TyDenote κ s ρ v → TyDenote κ t ρ v := by
  induction hsub with
  | refine hent =>
      rename_i b r₁ r₂
      intro ρ hΓ v hs
      cases b with
      | int =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨n, hvn, hp₁⟩ := hs
        have hf : Formula.interp _ ρ (Refinement.subImp r₁ r₂) := hent ρ hΓ
        simp only [Refinement.subImp, Formula.interp] at hf
        exact ⟨n, hvn, hf n hp₁⟩
      | bool =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨bv, hvb, hp₁⟩ := hs
        have hf : Formula.interp _ ρ (Refinement.subImp r₁ r₂) := hent ρ hΓ
        simp only [Refinement.subImp, Formula.interp] at hf
        exact ⟨bv, hvb, hf bv hp₁⟩
  | arrow _ _ _hin _hout =>
      -- Arrow case requires TyDenote.rename (Stage B) to align cofinite witnesses.
      sorry

/-! ## T2 — Fundamental Lemma -/

theorem hastype_fundamental {κ Γ e t} (h : Hastype κ Γ e t) :
    ∀ {γ ρ}, EnvAgrees κ Γ γ ρ →
    ∃ v, BigStep (Exp.substEnv γ e) v ∧ TyDenote κ t ρ v := by
  induction h with
  | var hlk =>
      rename_i x t
      intro γ ρ hE
      obtain ⟨v, hlkγ, hv, hcl, hint, hbool⟩ := EnvAgrees.lookup_some hE hlk
      refine ⟨v, ?_, ?_⟩
      · rw [Exp.substEnv_var_lookup x γ v hlkγ hcl (EnvAgrees.allClosed hE)]
        cases v with
        | iconst _   => exact BigStep.iconst
        | bconst _   => exact BigStep.bconst
        | clos _     => exact BigStep.lam
      · cases t with
        | refine b r =>
            cases b with
            | int  =>
                simp only [TyDenote] at hv
                obtain ⟨n, hvn, hp⟩ := hv
                simp only [self, TyDenote]
                refine ⟨n, hvn, ?_⟩
                simp only [Refinement.interp, Formula.interp, Term.interp,
                           REnv.get, REnv.update, hint n hvn]
                refine ⟨?_, ?_⟩
                · -- Show: Formula.interp κ ρ' r.fmla where ρ' is ρ updated at nuName.
                  -- We have hp : Refinement.interp κ r ρ n; unfold same.
                  show Formula.interp _ (ρ.update .int nuName n) r.fmla
                  exact hp
                · simp
            | bool =>
                simp only [TyDenote] at hv
                obtain ⟨bv, hvb, hp⟩ := hv
                simp only [self, TyDenote]
                refine ⟨bv, hvb, ?_⟩
                simp only [Refinement.interp, Formula.interp, Term.interp,
                           REnv.get, REnv.update, hbool bv hvb]
                refine ⟨?_, ?_⟩
                · show Formula.interp _ (ρ.update .bool nuName bv) r.fmla
                  exact hp
                · simp
        | arrow _ _ =>
            simp only [self]
            exact hv
  | int_const =>
      rename_i n
      intro γ ρ _
      refine ⟨.iconst n, ?_, ?_⟩
      · rw [Exp.substEnv_iconst]; exact BigStep.iconst
      · simp only [prim, TyDenote]
        refine ⟨n, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp]
  | bool_const =>
      rename_i b
      intro γ ρ _
      refine ⟨.bconst b, ?_, ?_⟩
      · rw [Exp.substEnv_bconst]; exact BigStep.bconst
      · simp only [primBool, TyDenote]
        refine ⟨b, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp]
  | ann _ ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      refine ⟨v, ?_, hv⟩
      rw [Exp.substEnv_ann]
      exact BigStep.ann hbs
  | sub _ hsub ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      exact ⟨v, hbs, subtyp_sound hsub (EnvAgrees.toModelsEnv hE) hv⟩
  | add_var _ _ =>
      -- Needs side conditions `x ≠ nuName`, `y ≠ nuName` on the typing rule
      -- so the ρ-update at nuName doesn't clobber the slots for `x`/`y`.
      -- See [Typing.lean]/[Declarative.lean] `add_var` rule.
      sorry
  | leq_var _ _ =>
      -- Same side-condition gap as `add_var`.
      sorry
  | not_var _ =>
      sorry
  | and_var _ _ =>
      sorry
  | lam L _ _ =>
      -- Cofinite λ-case: requires `Exp.subst_intro` and `TyDenote.rename`.
      sorry
  | app _ _ _ _ =>
      -- App needs the arrow LR's value-opening; deferred until rename keystone is in place.
      sorry
  | letin L _ _ _ _ =>
      sorry
  | ite hlk _ _ _ _ =>
      sorry

/-! ## T3 — Closed-term type safety (corollary of T2) -/

theorem type_safety {κ : KEnv} {e : Exp} {t : Ty} (h : Hastype κ [] e t) :
    ∃ v, BigStep e v ∧ TyDenote κ t REnv.empty v := by
  obtain ⟨v, hbs, hv⟩ :=
    hastype_fundamental h (γ := []) (ρ := REnv.empty) (by simp [EnvAgrees])
  exact ⟨v, by simpa [Exp.substEnv] using hbs, hv⟩

/-! ## T4 — End-to-end VCGen safety -/

theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty} (h : topVC κ [] e t) :
    ∃ v, BigStep e v ∧ TyDenote κ t REnv.empty v :=
  type_safety (topVC_decl_sound _ _ _ h)
