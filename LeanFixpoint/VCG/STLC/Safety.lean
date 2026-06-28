import LeanFixpoint.VCG.STLC.Semantics
import LeanFixpoint.VCG.STLC.Declarative
import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.VCG.STLC.Model

open STLC

/-! # Refinement Type Safety for STLC (LN + deep refinements + κ)

  We prove four headline results:

    (T1) `subtyp_sound`         — Subtyping is semantic inclusion of denotations.
    (T2) `hastype_fundamental`  — Well-typed terms evaluate to values in their
                                   denotation, under a closing value substitution.
    (T3) `type_safety`          — Closed-term safety (corollary of T2).
    (T4) `vcgen_safety`         — End-to-end VCGen safety:
                                   `topVC κ [] e t → ∃ v, e ⇓ v ∧ ⟦t⟧κ γ_∅ v`.

  All four are κ-indexed and operate over the new locally-nameless syntax with
  deep `Formula` refinements. The arrow case of the logical relation is stated
  in the canonical cofinite form (`∃ L, ∀ x ∉ L, …`), with the rename keystone
  (`TyDenote.rename`) proved as a separate lemma.
-/

namespace STLC

private theorem mem_TEnv_dom {Γ : TEnv} {x : EVar} {t : Ty} (h : (x, t) ∈ Γ) :
    x ∈ TEnv.dom Γ := by
  induction Γ with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [TEnv.dom, List.mem_cons]
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · left; rfl
    · right; exact ih h


end STLC


/-- Every value in the denotation is closed (no free names). The refinement
    cases follow from `Val.fv` of `iconst`/`bconst` being empty; the arrow
    case is required by the LR definition. -/
theorem TyDenote.closed {κ : KEnv} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ t γ v) : Val.closed v := by
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

/-! ## Closing environment

  `EnvCloses κ Γ γ` says: `γ` assigns each Γ-binding a value in that binding's
  logical relation. The value at `x` is simply `γ.map x`. It is the strengthening
  of `ModelsEnv` that also constrains arrow-typed bindings (which `var` needs to
  recover a closure). Duplicate keys are tolerated (head-shadowed entries from
  `ite`'s context). -/
def EnvCloses : KEnv → TEnv → REnv → Prop
  | _, [],          _ => True
  | κ, (x, t) :: Γ, γ => TyDenote κ t γ (γ.map x) ∧ EnvCloses κ Γ γ

/-- Every value in the denotation is locally closed (Val.lc). -/
theorem TyDenote.lc {κ : KEnv} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ t γ v) : Val.lc v := by
  cases t with
  | refine b r =>
    cases b with
    | int  => simp only [TyDenote] at h; obtain ⟨n, hvn, _⟩ := h; subst hvn; exact True.intro
    | bool => simp only [TyDenote] at h; obtain ⟨b, hvb, _⟩ := h; subst hvb; exact True.intro
  | arrow s t =>
    simp only [TyDenote] at h; obtain ⟨_, hvc, hlc, _, _⟩ := h; subst hvc; exact hlc

/-- `EnvCloses` projects to `ModelsEnv`: each refined Γ-binding's refinement
    holds at its γ-slot value `γ.map x`. (Structural, so head-shadowed bindings
    are also constrained — no `Γ.NoDup` needed.) -/
theorem EnvCloses.toModelsEnv :
    ∀ {κ Γ γ}, EnvCloses κ Γ γ → ModelsEnv κ γ Γ
  | _, [],                    _, _ => by simp [ModelsEnv]
  | _, (x, .refine b r) :: Γ, γ, h => by
      obtain ⟨hv, hΓ⟩ := h
      have hrest := EnvCloses.toModelsEnv hΓ
      cases b with
      | int  =>
        simp only [TyDenote] at hv
        obtain ⟨n, hmap, hp⟩ := hv
        refine ⟨⟨n, hmap⟩, ?_, hrest⟩
        simp only [REnv.get, REnv.lookup, hmap, Val.proj]; exact hp
      | bool =>
        simp only [TyDenote] at hv
        obtain ⟨bv, hmap, hp⟩ := hv
        refine ⟨⟨bv, hmap⟩, ?_, hrest⟩
        simp only [REnv.get, REnv.lookup, hmap, Val.proj]; exact hp
  | _, (_, .arrow _ _) :: _,  _, h => by
      obtain ⟨_, hΓ⟩ := h
      simp only [ModelsEnv]; exact EnvCloses.toModelsEnv hΓ

/-- Looking up `x` in Γ recovers its denotation at the γ-slot value `γ.map x`. -/
theorem EnvCloses.lookup :
    ∀ {κ Γ γ}, EnvCloses κ Γ γ → ∀ {x t}, Γ.lookup x = some t → TyDenote κ t γ (γ.map x)
  | _, [],          _, _, _, _, hl => by simp [List.lookup] at hl
  | _, (y, s) :: Γ, γ, h, x, t, hl => by
      obtain ⟨hv, hΓ⟩ := h
      by_cases heq : x = y
      · subst heq
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
        exact hl ▸ hv
      · have hne_beq : (x == y) = false := by rw [beq_eq_false_iff_ne]; exact heq
        simp only [List.lookup, hne_beq] at hl
        exact EnvCloses.lookup hΓ hl

/-- Every Γ-bound name maps to a locally-closed value under `EnvCloses`. -/
theorem EnvCloses.mem_lc :
    ∀ {κ Γ γ}, EnvCloses κ Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.lc (γ.map x)
  | _, [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | _, (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.lc hv
      · exact EnvCloses.mem_lc hΓ hx

/-- Every Γ-bound name maps to a closed value (no free names) under `EnvCloses`. -/
theorem EnvCloses.mem_closed :
    ∀ {κ Γ γ}, EnvCloses κ Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.closed (γ.map x)
  | _, [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | _, (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.closed hv
      · exact EnvCloses.mem_closed hΓ hx

/-! ## extendBy commutativity and extendBy_fresh -/

/-- `extendBy` at two different variables commutes. -/
private theorem REnv.write_comm (γ : REnv) (x z : EVar) (va va' : Val)
    (hxz : x ≠ z) :
    (γ.write z va').write x va =
    (γ.write x va).write z va' := by
  apply REnv.ext; funext w
  by_cases hxw : x = w <;> by_cases hzw : z = w <;> simp_all

/-- Helper: updating γ at a fresh x (x ∉ r.rawfv, x ∉ r.named, x ≠ nuName)
    does not change Refinement.interp. -/
private theorem Refinement.interp_write_fresh {κ : KEnv} {b : Base} (r : Refinement b)
    (x : EVar) (va : Val) (γ : REnv)
    (hx : x ∉ Refinement.rawfv r) (hxn : x ∉ Refinement.named r) (hxν : x ≠ nuName)
    {w : b.interp} :
    Refinement.interp κ r γ w ↔ Refinement.interp κ r (γ.write x va) w := by
  -- `extendBy s γ x va = γ.write x va`, and writing a fresh `x` is invisible to
  -- `interp` (the refinement never reads `x`). Commute the `ν`-binding write past
  -- the fresh `x`-write, then apply `*.interp_write_fresh`.
  have hcomm : (γ.write x va).update b nuName w = (γ.update b nuName w).write x va :=
    (REnv.write_update_comm b γ nuName w x va hxν).symm
  cases r with
  | fmla φ =>
    simp only [Refinement.rawfv, Refinement.named] at hx hxn
    simp only [Refinement.interp, hcomm]
    exact (Formula.interp_write_fresh φ x va (γ.update b nuName w) hx hxn).symm
  | kapp kn args =>
    have hargs : ∀ a ∈ args, x ∉ Term.fv a.2 := fun a ha hm =>
      hx (by simp only [Refinement.rawfv, List.mem_flatMap]; exact ⟨a, ha, hm⟩)
    simp only [Refinement.interp, hcomm]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    congr 1
    exact (Term.interp_write_fresh a.2 x va (γ.update b nuName w) (hargs a ha)).symm

/-- Combined Iff proved by strong induction on `t.skel`.
    Derives both `extendBy_fresh` and `of_extendBy_fresh` as corollaries. -/
private theorem TyDenote.extendBy_fresh_iff_aux (n : Nat) :
    ∀ (κ : KEnv) (t : Ty) (_ : t.skel ≤ n) (γ : REnv) (v : Val)
      (x : EVar) (va : Val)
      (_ : x ∉ t.fv) (_ : x ∉ Ty.named t) (_ : x ≠ nuName),
      TyDenote κ t γ v ↔ TyDenote κ t (γ.write x va) v := by
  induction n with
  | zero =>
    intro κ t hn γ v x va hx hxn hxν
    match t with
    | .refine b r =>
      have hx' := Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      cases b <;> simp only [TyDenote] <;> constructor
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mp hp⟩
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mpr hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mp hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mpr hp⟩
    | .arrow _ _ => simp [Ty.skel] at hn
  | succ n ih =>
    intro κ t hn γ v x va hx hxn hxν
    match t with
    | .refine b r =>
      have hx' := Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      cases b <;> simp only [TyDenote] <;> constructor
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mp hp⟩
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mpr hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mp hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mpr hp⟩
    | .arrow s' t' =>
      simp only [Ty.skel] at hn
      have hns' : s'.skel ≤ n := by omega
      have hnt' : t'.skel ≤ n := by omega
      simp only [Ty.fv, List.mem_append, not_or] at hx
      simp only [Ty.named, List.mem_append, not_or] at hxn
      simp only [TyDenote]
      constructor
      · -- extendBy_fresh direction: γ → extendBy s γ x va
        intro ⟨body, hvclos, hlc, hcl, hLR⟩
        refine ⟨body, hvclos, hlc, hcl, fun va' htd_va' => ?_⟩
        have htd_va'_γ : TyDenote κ s' γ va' :=
          (ih κ s' hns' γ va' x va hx.1 hxn.1 hxν).mpr htd_va'
        obtain ⟨vr, hbs_vr, htd_vr⟩ := hLR va' htd_va'_γ
        have hnt'va : (t'.substBV va').skel ≤ n := by rw [Ty.skel_substBV]; exact hnt'
        -- x ∉ (t'.substBV va').fv and named: sorried, follows from x ∉ t'.fv/named
        have hx_t'va : x ∉ (t'.substBV va').fv := by
          grind [Ty.fv_substBV_not_mem]
        have hxn_t'va : x ∉ Ty.named (t'.substBV va') := by
          grind [Ty.named_substBV_not_mem]
        exact ⟨vr, hbs_vr,
          (ih κ (t'.substBV va') hnt'va γ vr x va hx_t'va hxn_t'va hxν).mp htd_vr⟩
      · -- of_extendBy_fresh direction: extendBy s γ x va → γ
        intro ⟨body, hvclos, hlc, hcl, hLR⟩
        refine ⟨body, hvclos, hlc, hcl, fun va' htd_va' => ?_⟩
        have htd_va'_ext : TyDenote κ s' (γ.write x va) va' :=
          (ih κ s' hns' γ va' x va hx.1 hxn.1 hxν).mp htd_va'
        obtain ⟨vr, hbs_vr, htd_vr⟩ := hLR va' htd_va'_ext
        have hnt'va : (t'.substBV va').skel ≤ n := by rw [Ty.skel_substBV]; exact hnt'
        have hx_t'va : x ∉ (t'.substBV va').fv := by
          grind [Ty.fv_substBV_not_mem]
        have hxn_t'va : x ∉ Ty.named (t'.substBV va') := by
          grind [Ty.named_substBV_not_mem]
        exact ⟨vr, hbs_vr,
          (ih κ (t'.substBV va') hnt'va γ vr x va hx_t'va hxn_t'va hxν).mpr htd_vr⟩

/-- TyDenote is monotone under extension at a variable x that doesn't appear
    freely in t or as a named binder in t's formulas. -/
theorem TyDenote.extendBy_fresh {κ : KEnv} {t : Ty} {γ : REnv} {v : Val}
    (x : EVar) (va : Val)
    (hx : x ∉ t.fv) (hxn : x ∉ Ty.named t) (hxν : x ≠ nuName)
    (h : TyDenote κ t γ v) :
    TyDenote κ t (γ.write x va) v := by
  cases t with
  | refine b r =>
    cases b with
    | int =>
      simp only [TyDenote] at h ⊢
      obtain ⟨n, hvn, hp⟩ := h
      refine ⟨n, hvn, ?_⟩
      have hx' : x ∉ Refinement.rawfv r :=
        Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      exact (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mp hp
    | bool =>
      simp only [TyDenote] at h ⊢
      obtain ⟨bv, hvb, hp⟩ := h
      refine ⟨bv, hvb, ?_⟩
      have hx' : x ∉ Refinement.rawfv r :=
        Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      exact (Refinement.interp_write_fresh r x va γ hx' hxn' hxν).mp hp
  | arrow s' t' =>
    exact (TyDenote.extendBy_fresh_iff_aux (Ty.arrow s' t').skel κ (.arrow s' t') (by omega) γ v x va hx hxn hxν).mp h

/-- Reverse direction: TyDenote under extendBy at fresh x implies TyDenote at γ. -/
theorem TyDenote.of_extendBy_fresh {κ : KEnv} {t : Ty} {γ : REnv} {v : Val}
    (x : EVar) (va : Val)
    (hx : x ∉ t.fv) (hxn : x ∉ Ty.named t) (hxν : x ≠ nuName)
    (h : TyDenote κ t (γ.write x va) v) :
    TyDenote κ t γ v :=
  (TyDenote.extendBy_fresh_iff_aux t.skel κ t (by omega) γ v x va hx hxn hxν).mpr h

private theorem TyDenote.substBV_iff_aux (n : Nat) :
      ∀ (j : Nat) (κ : KEnv) (t : Ty) (_ : t.skel ≤ n) (s : Ty) (x : EVar) (γ : REnv)
        (va : Val) (v : Val)
        (_ : x ∉ t.fv) (_ : x ∉ Ty.named t) (_ : x ≠ nuName)
        (_ : Ty.WFBVarCtx (List.replicate j none ++ [s.optBase]) t)
        (_ : TyDenote κ s γ va),
        TyDenote κ (t.substBV_aux j va) γ v ↔
        TyDenote κ (t.openVar j x) (γ.write x va) v := by
  induction n with
  | zero =>
    intro j κ t hsk
    cases t <;> simp at hsk
    rename_i b r
    intro s x γ va v hxf hxn hxnn hwfb htd
    simp only [Ty.WFBVarCtx] at hwfb
    simp only [Ty.fv, Ty.named] at hxf hxn
    have hx_rfv : x ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r x hxf hxnn
    cases va with
    | iconst n =>
      cases s with
      | arrow s_d s_c => simp [TyDenote] at htd
      | refine sb r' =>
        cases sb with
        | int =>
          simp only [Ty.optBase] at hwfb
          simp only [Ty.substBV_aux, Ty.openVar]
          -- inner `.bool` opening is a no-op (WF: only `.int` BVars at this level)
          rw [Refinement.openBVar_noop (r.openBVar .int j x) .bool j x (by
                intro hbv
                rw [Refinement.hasBVar_openBVar_other r .bool .int j j x (Or.inl (by decide))] at hbv
                exact absurd (hwfb .bool j hbv) (by simp))]
          cases b <;> simp only [TyDenote] <;>
            exact ⟨fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .int j n x γ hx_rfv hxn hxnn).mp h⟩,
                   fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .int j n x γ hx_rfv hxn hxnn).mpr h⟩⟩
        | bool => simp [TyDenote] at htd
    | bconst bv =>
      cases s with
      | arrow s_d s_c => simp [TyDenote] at htd
      | refine sb r' =>
        cases sb with
        | bool =>
          simp only [Ty.optBase] at hwfb
          simp only [Ty.substBV_aux, Ty.openVar]
          rw [Refinement.openBVar_noop r .int j x (by
                intro hbv; exact absurd (hwfb .int j hbv) (by simp))]
          cases b <;> simp only [TyDenote] <;>
            exact ⟨fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .bool j bv x γ hx_rfv hxn hxnn).mp h⟩,
                   fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .bool j bv x γ hx_rfv hxn hxnn).mpr h⟩⟩
        | int => simp [TyDenote] at htd
    | clos body =>
      simp only [Ty.substBV_aux, Ty.openVar]
      cases s with
      | arrow s_d s_c =>
        simp only [Ty.optBase] at hwfb
        rw [Refinement.openBVar_noop r .int j x (by
              intro hbv; exact absurd (hwfb .int j hbv) (by simp)),
            Refinement.openBVar_noop r .bool j x (by
              intro hbv; exact absurd (hwfb .bool j hbv) (by simp))]
        cases b <;> simp only [TyDenote] <;>
          exact ⟨fun ⟨m, hm, h⟩ =>
                   ⟨m, hm, (Refinement.interp_write_fresh r x (.clos body) γ
                            hx_rfv hxn hxnn).mp h⟩,
                 fun ⟨m, hm, h⟩ =>
                   ⟨m, hm, (Refinement.interp_write_fresh r x (.clos body) γ
                            hx_rfv hxn hxnn).mpr h⟩⟩
      | refine sb r' =>
        cases sb with
        | int  => simp only [TyDenote] at htd; obtain ⟨_, h, _⟩ := htd; simp at h
        | bool => simp only [TyDenote] at htd; obtain ⟨_, h, _⟩ := htd; simp at h
  | succ n ih =>
    intro j κ t hsk s x γ va v hxf hxn hxν hwfb htd
    -- If t.skel ≤ n, delegate directly to IH
    by_cases hn : t.skel ≤ n
    · exact ih j κ t hn s x γ va v hxf hxn hxν hwfb htd
    -- Otherwise t.skel = n+1, so t must be an arrow type (refine has skel 0)
    · match t with
      | .refine b r =>
        simp [Ty.skel] at hn
      | .arrow s' t' =>
        simp only [Ty.skel] at hsk hn
        have hns' : s'.skel ≤ n := by omega
        have hnt' : t'.skel ≤ n := by omega
        simp only [Ty.fv, List.mem_append, not_or] at hxf hxn
        -- Destructure WFBVarCtx for arrow (it's a def, not And, so need explicit obtain)
        obtain ⟨hwfb_s', hwfb_t'⟩ : Ty.WFBVarCtx (List.replicate j none ++ [s.optBase]) s' ∧
            Ty.WFBVarCtx (s'.optBase :: List.replicate j none ++ [s.optBase]) t' := hwfb
        simp only [Ty.substBV_aux, Ty.openVar, TyDenote]
        -- Helper: WF for t'.substBV_aux 0 va' at level j+1
        -- Derives compat from TyDenote κ (s'.substBV_aux j va) γ va' and builds WFBVarCtx
        have mk_wf_cod : ∀ va',
            TyDenote κ (s'.substBV_aux j va) γ va' →
            Ty.WFBVarCtx (List.replicate (j+1) none ++ [s.optBase]) (t'.substBV_aux 0 va') := by
          intro va' htd_va'_γ
          have hci' : s'.optBase = some .int → ∃ n, va' = .iconst n := by
            cases s' with
            | arrow _ _ => simp [Ty.optBase]
            | refine sb r =>
              cases sb with
              | bool => simp [Ty.optBase]
              | int =>
                intro _
                have : ∃ r', (Ty.refine .int r).substBV_aux j va = .refine .int r' := by
                  rcases va with n' | bv' | body
                  · exact ⟨r.substBV .int j n', rfl⟩
                  · exact ⟨r.substBV .bool j bv', rfl⟩
                  · exact ⟨r, rfl⟩
                obtain ⟨r', hr'⟩ := this
                rw [hr'] at htd_va'_γ; simp only [TyDenote] at htd_va'_γ
                exact ⟨_, htd_va'_γ.choose_spec.1⟩
          have hcb' : s'.optBase = some .bool → ∃ bv, va' = .bconst bv := by
            cases s' with
            | arrow _ _ => simp [Ty.optBase]
            | refine sb r =>
              cases sb with
              | int => simp [Ty.optBase]
              | bool =>
                intro _
                have : ∃ r', (Ty.refine .bool r).substBV_aux j va = .refine .bool r' := by
                  rcases va with n' | bv' | body
                  · exact ⟨r.substBV .int j n', rfl⟩
                  · exact ⟨r.substBV .bool j bv', rfl⟩
                  · exact ⟨r, rfl⟩
                obtain ⟨r', hr'⟩ := this
                rw [hr'] at htd_va'_γ; simp only [TyDenote] at htd_va'_γ
                exact ⟨_, htd_va'_γ.choose_spec.1⟩
          have h := Ty.WFBVarCtx_substBV_aux_prefix t' [] s'.optBase
            (List.replicate j none ++ [s.optBase]) va'
            (by simpa using hwfb_t') hci' hcb'
          simpa [List.replicate_succ] using h
        constructor
        · -- LHS (substBV/γ) → RHS (openVar/extendBy)
          rintro ⟨body, rfl, hlc, hcl, hLR⟩
          refine ⟨body, rfl, hlc, hcl, fun va' htd_va' => ?_⟩
          simp [Ty.named] at hxn
          have htd_va'_γ : TyDenote κ (s'.substBV_aux j va) γ va' :=
            (ih j κ s' hns' s x γ va va' hxf.1 hxn.1 hxν hwfb_s' htd).mpr htd_va'
          obtain ⟨vr, hbs, htd_vr⟩ := hLR va' htd_va'_γ
          refine ⟨vr, hbs, ?_⟩
          -- htd_vr : TyDenote κ ((t'.substBV_aux (j+1) va).substBV va') γ vr
          simp only [Ty.substBV] at htd_vr ⊢
          -- Now htd_vr uses substBV_aux 0; rewrite via comm
          rw [Ty.substBV_aux_comm t' va (j+1) va' 0 (by omega)] at htd_vr
          rw [← Ty.openVar_substBV_aux_comm t' (j+1) x va' 0 (by omega)]
          exact (ih (j+1) κ (t'.substBV_aux 0 va') (by rw [←Ty.substBV] ; rw [Ty.skel_substBV]; exact hnt')
                    s x γ va vr
                    (Ty.fv_substBV_not_mem t' x va' hxf.2)
                    (Ty.named_substBV_not_mem t' x va' hxn.2)
                    hxν (mk_wf_cod va' htd_va'_γ) htd).mp htd_vr
        · -- RHS (openVar/extendBy) → LHS (substBV/γ)
          rintro ⟨body, rfl, hlc, hcl, hLR⟩
          refine ⟨body, rfl, hlc, hcl, fun va' htd_va'_γ => ?_⟩
          simp [Ty.named] at hxn
          have htd_va' : TyDenote κ (s'.openVar j x) (γ.write x va) va' :=
            (ih j κ s' hns' s x γ va va' hxf.1 hxn.1 hxν hwfb_s' htd).mp htd_va'_γ
          obtain ⟨vr, hbs, htd_vr⟩ := hLR va' htd_va'
          refine ⟨vr, hbs, ?_⟩
          -- htd_vr : TyDenote κ ((t'.openVar (j+1) x).substBV va') (extendBy s γ x va) vr
          simp only [Ty.substBV] at htd_vr ⊢
          rw [← Ty.openVar_substBV_aux_comm t' (j+1) x va' 0 (by omega)] at htd_vr
          have htd_vr' := (ih (j+1) κ (t'.substBV_aux 0 va') (by rw [←Ty.substBV] ; rw [Ty.skel_substBV]; exact hnt')
                    s x γ va vr
                    (Ty.fv_substBV_not_mem t' x va' hxf.2)
                    (Ty.named_substBV_not_mem t' x va' hxn.2)
                    hxν (mk_wf_cod va' htd_va'_γ) htd).mpr htd_vr
          rw [Ty.substBV_aux_comm]
            <;> grind

/-- `substBV va` in TyDenote corresponds to `openVar 0 x` with `extendBy s γ x va`,
    when x is fresh for t, va is compatible with s (TyDenote κ s γ va), and t is
    well-formed (WFBVarCtx [s.optBase] t) so that only the correct-base BVars appear. -/
theorem TyDenote.substBV_iff (κ : KEnv) (t : Ty) (s : Ty) (x : EVar) (γ : REnv)
    (va : Val) (v : Val)
    (hx_fv : x ∉ t.fv) (hx_named : x ∉ Ty.named t) (hxν : x ≠ nuName)
    (hWF : Ty.WFBVarCtx [s.optBase] t)
    (hcompat : TyDenote κ s γ va) :
    TyDenote κ (t.substBV va) γ v ↔
    TyDenote κ (t.openVar 0 x) (γ.write x va) v := by
  apply TyDenote.substBV_iff_aux t.skel
  · omega
  · assumption
  · assumption
  · assumption
  · simp ; assumption
  · assumption

/-- `EnvCloses` is preserved when extending `γ` at a name `x` fresh for Γ
    (the existing bindings never read `x`). -/
theorem EnvCloses.extendBy_fresh {κ Γ γ} (hE : EnvCloses κ Γ γ)
    (x : EVar) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) (hx_named : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName) :
    EnvCloses κ Γ (γ.write x va) := by
  induction Γ with
  | nil => exact True.intro
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    obtain ⟨htd, hΓ⟩ := hE
    simp only [TEnv.dom, List.mem_cons, not_or] at hx_dom
    simp only [TEnv.tyFv, List.mem_append, not_or] at hx_fv
    simp only [TEnv.tyNamed, List.mem_append, not_or] at hx_named
    have hxy : x ≠ y := hx_dom.1
    refine ⟨?_, ih hΓ hx_dom.2 hx_fv.2 hx_named.2⟩
    rw [REnv.write_other γ x va hxy]
    exact TyDenote.extendBy_fresh x va hx_fv.1 hx_named.1 hxν htd

/-- Extend `EnvCloses` by prepending a fresh `(x, s)` binding whose value `va`
    is the value written at `x`. The single-env analogue of `EnvAgrees.extend`;
    the reflection clauses are gone since the slot value is `va` by `write_self`. -/
theorem EnvCloses.extend {κ Γ γ} (hE : EnvCloses κ Γ γ)
    (x : EVar) (s : Ty) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) (hx_named : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName)
    (htd : TyDenote κ s (γ.write x va) va) :
    EnvCloses κ ((x, s) :: Γ) (γ.write x va) := by
  refine ⟨?_, EnvCloses.extendBy_fresh hE x va hx_dom hx_fv hx_named hxν⟩
  rw [show (γ.write x va).map x = va by exact REnv.write_self γ x va]
  exact htd

/-! ## T1 — Subtyping is semantic inclusion of denotations -/

private theorem Subtyp.optBase_eq {κ Γ s t} (h : Subtyp κ Γ s t) : s.optBase = t.optBase := by
  cases h with
  | refine => rfl
  | arrow => simp [Ty.optBase]

/-- ModelsEnv is preserved when extending γ at z fresh from Γ. -/
private theorem ModelsEnv.extendBy_fresh_aux {κ : KEnv} {Γ : TEnv} {γ : REnv}
    (hm : ModelsEnv κ γ Γ) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_named : z ∉ TEnv.tyNamed Γ)
    (hzν : z ≠ nuName) :
    ModelsEnv κ (γ.write z va) Γ := by
  induction Γ with
  | nil => exact True.intro
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    simp only [TEnv.dom, List.mem_cons, not_or] at hz_dom
    simp only [TEnv.tyFv, List.mem_append, not_or] at hz_fv
    simp only [TEnv.tyNamed, List.mem_append, not_or] at hz_named
    cases t with
    | arrow s' t' =>
      simp only [ModelsEnv] at hm ⊢
      exact ih hm hz_dom.2 hz_fv.2 hz_named.2
    | refine b r =>
      simp only [ModelsEnv] at hm ⊢
      obtain ⟨hHB, hhead, htail⟩ := hm
      have hzy : z ≠ y := hz_dom.1
      have hmap : (γ.write z va).map y = γ.map y :=
        REnv.write_other γ z va hzy
      refine ⟨?_, ?_, ih htail hz_dom.2 hz_fv.2 hz_named.2⟩
      · cases b with
        | int  => obtain ⟨n, hn⟩ := hHB; exact ⟨n, by rw [hmap]; exact hn⟩
        | bool => obtain ⟨c, hc⟩ := hHB; exact ⟨c, by rw [hmap]; exact hc⟩
      · have hz_rfv : z ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r z hz_fv.1 hzν
        have hz_rnamed : z ∉ Refinement.named r := by simpa [Ty.named] using hz_named.1
        have hget : REnv.get b (γ.write z va) y = REnv.get b γ y := by simp_all only [REnv.get, REnv.lookup]
        rw [hget]
        exact (Refinement.interp_write_fresh r z va γ hz_rfv hz_rnamed hzν).mp hhead

/-- Build ModelsEnv after prepending a fresh binding (z, s₂). -/
private theorem ModelsEnv.extendBy_cons {κ : KEnv} {Γ : TEnv} {γ : REnv}
    (hm : ModelsEnv κ γ Γ) (s₂ : Ty) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_named : z ∉ TEnv.tyNamed Γ)
    (hz_s2fv : z ∉ s₂.fv)
    (hz_s2named : z ∉ Ty.named s₂)
    (hzν : z ≠ nuName)
    (htd_va : TyDenote κ s₂ γ va) :
    ModelsEnv κ (γ.write z va) ((z, s₂) :: Γ) := by
  have htail := ModelsEnv.extendBy_fresh_aux hm z va hz_dom hz_fv hz_named hzν
  cases s₂ with
  | arrow s' t' => simp only [ModelsEnv]; exact htail
  | refine b r =>
    simp only [ModelsEnv]
    have hz_rfv : z ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r z hz_s2fv hzν
    have hz_rnamed : z ∉ Refinement.named r := by simpa [Ty.named] using hz_s2named
    cases b with
    | int =>
      simp only [TyDenote] at htd_va
      obtain ⟨n, hvn, hp⟩ := htd_va; subst hvn
      refine ⟨⟨n, ?_⟩, ?_, htail⟩
      · simp
      · simp only [REnv.get_update_same]
        exact (Refinement.interp_write_fresh r z (.iconst n) γ
                hz_rfv hz_rnamed hzν).mp hp
    | bool =>
      simp only [TyDenote] at htd_va
      obtain ⟨bv, hvb, hp⟩ := htd_va; subst hvb
      refine ⟨⟨bv, ?_⟩, ?_, htail⟩
      · simp
      · simp only [REnv.get_update_same]
        exact (Refinement.interp_write_fresh r z (.bconst bv) γ
                hz_rfv hz_rnamed hzν).mp hp

theorem subtyp_sound {κ Γ s t} (hsub : Subtyp κ Γ s t)
    (hWF_s : Ty.WFBVars s) (hWF_t : Ty.WFBVars t) :
    ∀ {γ}, ModelsEnv κ γ Γ → ∀ {v}, TyDenote κ s γ v → TyDenote κ t γ v := by
  induction hsub with
  | refine hent =>
      rename_i b r₁ r₂
      intro γ hΓ v hs
      cases b with
      | int =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨n, hvn, hp₁⟩ := hs
        exact ⟨n, hvn, hent γ hΓ n hp₁⟩
      | bool =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨bv, hvb, hp₁⟩ := hs
        exact ⟨bv, hvb, hent γ hΓ bv hp₁⟩
  | arrow hdom hfresh hcodom ih_hdom ih_hcodom =>
    rename_i Γ' s₁ t₁ s₂ t₂ x
    obtain ⟨hWF_s1, hWF_st1⟩ := hWF_s
    obtain ⟨hWF_s2, hWF_t2⟩ := hWF_t
    -- optBase equality from domain subtyping s₂ <: s₁
    have hopt_eq : s₂.optBase = s₁.optBase := by grind [Subtyp.optBase_eq]
    have hWF_st1' : Ty.WFBVarCtx [s₂.optBase] t₁ := hopt_eq ▸ hWF_st1
    -- Extract freshness facts for x from hfresh
    simp only [List.mem_append, List.mem_singleton, not_or] at hfresh
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx_Γdom, hx_Γfv⟩, hx_Γnamed⟩,
               hx_s1fv⟩, hx_s2fv⟩, hx_t1fv⟩, hx_t2fv⟩,
               hx_s1named⟩, hx_s2named⟩, hx_t1named⟩, hx_t2named⟩, hxν⟩ := hfresh
    intro γ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨body, hvc, hlc, hcl, hLR⟩ := htd
    refine ⟨body, hvc, hlc, hcl, fun va htd_va => ?_⟩
    -- Domain conversion (contravariant): s₂ <: s₁ so s₂-typed va is also s₁-typed
    have htd_va_s1 : TyDenote κ s₁ γ va := ih_hdom hWF_s2 hWF_s1 hm htd_va
    -- Apply the function body at s₁-typed va
    obtain ⟨vr, hbs, htd_vr_t1⟩ := hLR va htd_va_s1
    refine ⟨vr, hbs, ?_⟩
    -- Use x directly from the constructor (no fresh pick needed)
    have hWF_t1x : Ty.WFBVars (t₁.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₁ [] s₂.optBase x hWF_st1'
    have hWF_t2x : Ty.WFBVars (t₂.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₂ [] s₂.optBase x hWF_t2
    -- Convert t₁.substBV va ↔ t₁.openVar 0 x under extendBy s₂ γ x va
    rw [TyDenote.substBV_iff κ t₁ s₂ x γ va vr hx_t1fv hx_t1named hxν hWF_st1' htd_va]
      at htd_vr_t1
    -- Build extended model for ((x, s₂) :: Γ')
    have hm_ext : ModelsEnv κ (γ.write x va) ((x, s₂) :: Γ') :=
      ModelsEnv.extendBy_cons hm s₂ x va hx_Γdom hx_Γfv hx_Γnamed hx_s2fv hx_s2named hxν htd_va
    -- Apply codomain IH at x
    have htd_vr_t2 : TyDenote κ (t₂.openVar 0 x) (γ.write x va) vr :=
      ih_hcodom hWF_t1x hWF_t2x hm_ext htd_vr_t1
    -- Convert back: t₂.openVar 0 x ↔ t₂.substBV va
    exact (TyDenote.substBV_iff κ t₂ s₂ x γ va vr hx_t2fv hx_t2named hxν hWF_t2 htd_va).mpr
      htd_vr_t2

/-! ## T2 — Fundamental Lemma -/

theorem hastype_fundamental {κ Γ e t} (h : Hastype κ Γ e t) :
    ∀ {γ}, EnvCloses κ Γ γ →
    ∃ v, BigStep (Exp.substEnv γ e) v ∧ TyDenote κ t γ v := by
  induction h with
  | var hlk _ =>
      rename_i Γ x t hwf
      intro γ hE
      have hv := EnvCloses.lookup hE hlk
      refine ⟨γ.map x, ?_, ?_⟩
      · rw [Exp.substEnv_fvar]
        cases hvm : γ.map x with
        | iconst _   => exact BigStep.iconst
        | bconst _   => exact BigStep.bconst
        | clos _     => exact BigStep.lam
      · cases t with
        | refine b r =>
            cases b with
            | int  =>
                simp only [TyDenote] at hv
                obtain ⟨n, hmap, _⟩ := hv
                simp only [self, TyDenote]
                refine ⟨n, hmap, ?_⟩
                simp [Refinement.interp, Formula.interp, Term.interp,
                      REnv.get, REnv.lookup, hmap]
            | bool =>
                simp only [TyDenote] at hv
                obtain ⟨bv, hmap, _⟩ := hv
                simp only [self, TyDenote]
                refine ⟨bv, hmap, ?_⟩
                simp [Refinement.interp, Formula.interp, Term.interp,
                      REnv.get, REnv.lookup, hmap]
        | arrow _ _ =>
            simp only [self]
            exact hv
  | int_const =>
      rename_i n
      intro γ _
      refine ⟨.iconst n, ?_, ?_⟩
      · rw [Exp.substEnv_iconst]; exact BigStep.iconst
      · simp only [prim, TyDenote]
        refine ⟨n, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp]
  | bool_const =>
      rename_i b
      intro γ _
      refine ⟨.bconst b, ?_, ?_⟩
      · rw [Exp.substEnv_bconst]; exact BigStep.bconst
      · simp only [primBool, TyDenote]
        refine ⟨b, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp]
  | ann _ _ =>
      rename_i hht _ ih
      intro γ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      refine ⟨v, ?_, hv⟩
      rw [Exp.substEnv_ann]
      exact BigStep.ann hbs
  | sub hhs hsub hwf_t ih =>
      intro γ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      exact ⟨v, hbs, subtyp_sound hsub hhs.wf_bvars hwf_t (EnvCloses.toModelsEnv hE) hv⟩
  | add_var hlk₁ hlk₂ hxν hyν =>
      rename_i x y r₁ r₂
      intro γ hE
      have hv₁ := EnvCloses.lookup hE hlk₁
      simp only [TyDenote] at hv₁; obtain ⟨n₁, hγx, _⟩ := hv₁
      have hv₂ := EnvCloses.lookup hE hlk₂
      simp only [TyDenote] at hv₂; obtain ⟨n₂, hγy, _⟩ := hv₂
      have hx : Exp.substEnv γ (.fvar x) = .iconst n₁ := by simp [Exp.substEnv_fvar, hγx]
      have hy : Exp.substEnv γ (.fvar y) = .iconst n₂ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.iconst (n₁ + n₂), ?_, ?_⟩
      · rw [Exp.substEnv_add, hx, hy]; exact BigStep.add BigStep.iconst BigStep.iconst
      · simp only [TyDenote]; refine ⟨n₁ + n₂, rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        have hνy : (nuName == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hyν)
        simp [hνx, hνy, hγx, hγy]
  | leq_var hlk₁ hlk₂ hxν hyν =>
      rename_i x y r₁ r₂
      intro γ hE
      have hv₁ := EnvCloses.lookup hE hlk₁
      simp only [TyDenote] at hv₁; obtain ⟨n₁, hγx, _⟩ := hv₁
      have hv₂ := EnvCloses.lookup hE hlk₂
      simp only [TyDenote] at hv₂; obtain ⟨n₂, hγy, _⟩ := hv₂
      have hx : Exp.substEnv γ (.fvar x) = .iconst n₁ := by simp [Exp.substEnv_fvar, hγx]
      have hy : Exp.substEnv γ (.fvar y) = .iconst n₂ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.bconst (decide (n₁ ≤ n₂)), ?_, ?_⟩
      · rw [Exp.substEnv_leq, hx, hy]; exact BigStep.leq BigStep.iconst BigStep.iconst
      · simp only [TyDenote]; refine ⟨decide (n₁ ≤ n₂), rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        have hνy : (nuName == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hyν)
        simp only [REnv.get, REnv.lookup, beq_self_eq_true,
                   ↓reduceIte, hνx, hνy, hγx, hγy, Val.proj]
        constructor
        · intro h; exact decide_eq_true_iff.mp h
        · intro h; exact decide_eq_true_iff.mpr h
  | not_var hlk hxν =>
      rename_i x r
      intro γ hE
      have hv₁ := EnvCloses.lookup hE hlk
      simp only [TyDenote] at hv₁; obtain ⟨b, hγx, _⟩ := hv₁
      have hx : Exp.substEnv γ (.fvar x) = .bconst b := by simp [Exp.substEnv_fvar, hγx]
      refine ⟨.bconst (!b), ?_, ?_⟩
      · rw [Exp.substEnv_not, hx]; exact BigStep.not_ BigStep.bconst
      · simp only [TyDenote]; refine ⟨!b, rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        simp [hνx, hγx]
  | and_var hlkx hlky hxν hyν =>
      rename_i x y rx ry
      intro γ hE
      have hvx := EnvCloses.lookup hE hlkx
      simp only [TyDenote] at hvx; obtain ⟨bx, hγx, _⟩ := hvx
      have hvy := EnvCloses.lookup hE hlky
      simp only [TyDenote] at hvy; obtain ⟨by_, hγy, _⟩ := hvy
      have hxx : Exp.substEnv γ (.fvar x) = .bconst bx := by simp [Exp.substEnv_fvar, hγx]
      have hyy : Exp.substEnv γ (.fvar y) = .bconst by_ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.bconst (bx && by_), ?_, ?_⟩
      · rw [Exp.substEnv_and, hxx, hyy]; exact BigStep.and_ BigStep.bconst BigStep.bconst
      · simp only [TyDenote]; refine ⟨bx && by_, rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        have hνy : (nuName == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hyν)
        simp [hνx, hνy, hγx, hγy]
  | lam hwf_arr hfresh ih =>
      rename_i Γ' body s₁ s₂ x ih_fund
      intro γ hE
      rw [Exp.substEnv_lam]
      have hbody_dom : ∀ z ∈ body.fv, z ∈ TEnv.dom Γ' := by
        intro z hz
        obtain ⟨t', hzΓ⟩ := (Hastype.lam hwf_arr hfresh ih).fv_subset z (by simpa [Exp.fv] using hz)
        exact mem_TEnv_dom hzΓ
      refine ⟨.clos (Exp.substEnv γ body), BigStep.lam, ?_⟩
      simp only [TyDenote]
      refine ⟨Exp.substEnv γ body, rfl, ?_, ?_, ?_⟩
      · -- Val.lc
        simp only [Val.lc]
        exact Exp.substEnv_lc_at γ body 1
          (fun z hz => EnvCloses.mem_lc hE (hbody_dom z hz))
          (Hastype.lam hwf_arr hfresh ih).lc_at
      · -- Val.closed
        simp only [Val.closed, Val.fv]
        exact Exp.substEnv_fv_nil γ body
          (fun z hz => EnvCloses.mem_closed hE (hbody_dom z hz))
      · -- LR: for any va : s₁, produce vr evaluating body and in s₂.substBV va
        intro va htd_va
        -- x is the witness from the constructor; extract freshness facts
        simp [List.mem_append, not_or] at hfresh
        obtain ⟨hxΓ, hxΓfv, hxΓnamed, hxbody, hxs₁, hxs₂, hxs₁n, hxs₂n, hxν⟩ := hfresh
        have htd_va_x : TyDenote κ s₁ (γ.write x va) va :=
          TyDenote.extendBy_fresh x va hxs₁ hxs₁n hxν htd_va
        have hEx : EnvCloses κ ((x, s₁) :: Γ') (γ.write x va) :=
          EnvCloses.extend hE x s₁ va hxΓ hxΓfv hxΓnamed hxν htd_va_x
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_fund hEx
        rw [Exp.substEnv_write_openVar body γ va x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (hbody_dom w hw))] at hbs_vr
        have hWF_s₂ : Ty.WFBVarCtx [s₁.optBase] s₂ := hwf_arr.2
        exact ⟨vr, hbs_vr,
          (TyDenote.substBV_iff κ s₂ s₁ x γ va vr hxs₂ hxs₂n hxν hWF_s₂ htd_va).mpr htd_vr⟩
  | app h_fn h_arg hyfv hynamed hyν ih_fn ih_arg =>
      rename_i e₁ y s t
      intro γ hE
      -- Evaluate the function
      obtain ⟨v_fn, hbs_fn, htd_fn⟩ := ih_fn hE
      simp only [TyDenote] at htd_fn
      obtain ⟨body, hvclos, hlc_clos, hcl_clos, hLR⟩ := htd_fn
      subst hvclos
      -- Evaluate the argument (a variable `y`)
      obtain ⟨va, hbs_arg, htd_arg⟩ := ih_arg hE
      obtain ⟨vr, hbs_body, htd_vr⟩ := hLR va htd_arg
      -- Since the argument is the variable `y`, it evaluates to `γ.map y`, so the
      -- extension is the identity (`write y (γ.map y) = γ`) — no `HasBase` needed.
      have hext : γ.write y va = γ := by
        have hbs_raw : BigStep (Exp.substEnv γ (.fvar y)) (γ.map y) := by
          rw [Exp.substEnv_fvar]
          cases h : γ.map y with
          | iconst _ => exact BigStep.iconst
          | bconst _ => exact BigStep.bconst
          | clos _   => exact BigStep.lam
        have hva_eq : va = γ.map y := BigStep.det hbs_arg hbs_raw
        subst hva_eq
        exact REnv.write_idem γ y
      have hWF_t : Ty.WFBVarCtx [s.optBase] t := h_fn.wf_bvars.2
      have htd_vr_y : TyDenote κ (t.openVar 0 y) γ vr := by
        rw [← hext]
        exact (TyDenote.substBV_iff κ t s y γ va vr hyfv hynamed hyν hWF_t htd_arg).mp htd_vr
      refine ⟨vr, ?_, htd_vr_y⟩
      rw [Exp.substEnv_app]
      exact BigStep.app hbs_fn hbs_arg hbs_body
  | @letin Γ' e₁ e₂ s' t' x hwfbv hht xf hhto ih₁ ih₂ =>
      intro γ hE
      obtain ⟨v₁, hbs₁, htd₁⟩ := ih₁ hE
      have he₂_dom : ∀ w ∈ e₂.fv, w ∈ TEnv.dom Γ' := by
        intro w hw
        obtain ⟨t'', hwΓ⟩ := (Hastype.letin hwfbv hht xf hhto).fv_subset w
          (by simp only [Exp.fv]; exact List.mem_append_right _ hw)
        exact mem_TEnv_dom hwΓ
      simp [List.mem_append, not_or] at xf
      obtain ⟨hxΓ, hxΓfv, hxΓnamed, hxbody, hxs, hxt, hxsn, hxtn, hxν⟩ := xf
      have htd₁_x : TyDenote κ s' (γ.write x v₁) v₁ :=
        TyDenote.extendBy_fresh x v₁ hxs hxsn hxν htd₁
      have hEx : EnvCloses κ ((x, s') :: Γ') (γ.write x v₁) :=
        EnvCloses.extend hE x s' v₁ hxΓ hxΓfv hxΓnamed hxν htd₁_x
      obtain ⟨vr, hbs₂, htd_vr⟩ := ih₂ hEx
      rw [Exp.substEnv_write_openVar e₂ γ v₁ x 0 hxbody
            (fun w hw => EnvCloses.mem_lc hE (he₂_dom w hw))] at hbs₂
      have htd_vr_γ : TyDenote κ t' γ vr :=
        TyDenote.of_extendBy_fresh x v₁ hxt hxtn hxν htd_vr
      rw [Exp.substEnv_letin]
      exact ⟨vr, BigStep.letin hbs₁ hbs₂, htd_vr_γ⟩
  | ite hlk hxν hfresh _ h₁ h₂ ih_e₁ ih_e₂ =>
      rename_i Γ x y e₁ e₂ r t _
      intro γ hE
      have htd_x := EnvCloses.lookup hE hlk
      simp only [TyDenote] at htd_x
      obtain ⟨bx, hγx, _⟩ := htd_x
      have hxfv : Exp.substEnv γ (.fvar x) = .bconst bx := by simp [Exp.substEnv_fvar, hγx]
      -- `nuName ≠ x` lets the guard refinement (which reads `x`) simplify.
      have hνx : (nuName == x) = false := by
        simp only [beq_eq_false_iff_ne]; exact fun he => hxν he.symm
      -- `y` (the fresh guard) is not free in either branch.
      have hy_e₁ : y ∉ e₁.fv := fun hm => hfresh (by simp [hm])
      have hy_e₂ : y ∉ e₂.fv := fun hm => hfresh (by simp [hm])
      -- Fresh-guard refinements read `x` free (not ν); `y`'s own value is irrelevant.
      let r_true : Refinement .bool :=
        .fmla (.eqB (.fvar .bool x) (.const .bool true))
      let r_false : Refinement .bool :=
        .fmla (.eqB (.fvar .bool x) (.const .bool false))
      -- Freshness facts for `y` (all from `hfresh`).
      have hy_dom : y ∉ TEnv.dom Γ := fun hm => hfresh (by simp [hm])
      have hy_tyfv : y ∉ TEnv.tyFv Γ := fun hm => hfresh (by simp [hm])
      have hy_tynamed : y ∉ TEnv.tyNamed Γ := fun hm => hfresh (by simp [hm])
      have hy_tfv : y ∉ t.fv := fun hm => hfresh (by simp [hm])
      have hy_tnamed : y ∉ Ty.named t := fun hm => hfresh (by simp [hm])
      have hyx : y ≠ x := fun he => hfresh (by simp [he])
      have hyν : y ≠ nuName := fun he => hfresh (by simp [he])
      -- Under one map, the fresh guard `y` occupies a real `bconst` cell, so we
      -- extend `γ` at `y` and recover the result type with `of_extendBy_fresh`.
      cases bx with
      | true =>
        have htd_guard : TyDenote κ (.refine .bool r_true)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, r_true]
          refine ⟨γ.bools y, rfl, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup,
                Ne.symm hxν, hyx, hγx]
        have hE₁ : EnvCloses κ ((y, .refine .bool r_true) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_true) (.bconst (γ.bools y))
            hy_dom hy_tyfv hy_tynamed hyν htd_guard
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_e₁ hE₁
        rw [Exp.substEnv_write_fresh e₁ γ y (.bconst (γ.bools y)) hy_e₁] at hbs_vr
        refine ⟨vr, ?_,
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y))
            hy_tfv hy_tnamed hyν htd_vr⟩
        rw [Exp.substEnv_ite, hxfv]
        exact BigStep.ite_t BigStep.bconst hbs_vr
      | false =>
        have htd_guard : TyDenote κ (.refine .bool r_false)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, r_false]
          refine ⟨γ.bools y, rfl, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup,
                Ne.symm hxν, hyx, hγx]
        have hE₂ : EnvCloses κ ((y, .refine .bool r_false) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_false) (.bconst (γ.bools y))
            hy_dom hy_tyfv hy_tynamed hyν htd_guard
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_e₂ hE₂
        rw [Exp.substEnv_write_fresh e₂ γ y (.bconst (γ.bools y)) hy_e₂] at hbs_vr
        refine ⟨vr, ?_,
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y))
            hy_tfv hy_tnamed hyν htd_vr⟩
        rw [Exp.substEnv_ite, hxfv]
        exact BigStep.ite_f BigStep.bconst hbs_vr

/-! ## T3 — Closed-term type safety (corollary of T2) -/

theorem type_safety {κ : KEnv} {e : Exp} {t : Ty} (h : Hastype κ [] e t) :
    ∃ v, BigStep e v ∧ TyDenote κ t REnv.empty v := by
  have hfv : e.fv = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
      obtain ⟨t', ht'⟩ := h.fv_subset z hz; simp at ht'
  obtain ⟨v, hbs, hv⟩ :=
    hastype_fundamental h (γ := REnv.empty) (by simp [EnvCloses])
  rw [Exp.substEnv_closed REnv.empty e hfv] at hbs
  exact ⟨v, hbs, hv⟩

/-! ## T4 — End-to-end VCGen safety

  The POPL headline: VCGen soundness composes with the logical-relations
  fundamental lemma to give end-to-end refinement type safety for `topVC`. -/

theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t) :
    ∃ v, BigStep e v ∧ TyDenote κ t REnv.empty v :=
  type_safety (topVC_decl_sound κ e t hE ht h)
