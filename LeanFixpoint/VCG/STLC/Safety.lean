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
        ∀ va, TyDenote κ s ρ va →
          ∃ vr, BigStep (body.openVal 0 va) vr ∧
                TyDenote κ (t.substBV va) ρ vr
termination_by _ t _ _ => t.skel
decreasing_by
  all_goals simp_wf
  · omega
  · omega

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

/-- Every value in the denotation is locally closed (Val.lc). -/
theorem TyDenote.lc {κ : KEnv} {t : Ty} {ρ : REnv} {v : Val}
    (h : TyDenote κ t ρ v) : Val.lc v := by
  cases t with
  | refine b r =>
    cases b with
    | int  => simp only [TyDenote] at h; obtain ⟨n, hvn, _⟩ := h; subst hvn; exact True.intro
    | bool => simp only [TyDenote] at h; obtain ⟨b, hvb, _⟩ := h; subst hvb; exact True.intro
  | arrow s t =>
    simp only [TyDenote] at h; obtain ⟨_, hvc, hlc, _, _⟩ := h; subst hvc; exact hlc

/-- `EnvAgrees` implies pointwise closedness of `γ`. -/
theorem EnvAgrees.allClosed :
    ∀ {κ Γ γ ρ}, EnvAgrees κ Γ γ ρ → Subst.AllVClosed γ
  | _, [],            [],          _, _ => True.intro
  | _, (_, _) :: _,   (_, v) :: γ, _, h => by
      obtain ⟨_, hΓ, hv, _, _⟩ := h
      exact ⟨TyDenote.closed hv, EnvAgrees.allClosed hΓ⟩
  | _, [],            _ :: _,      _, h => by cases h
  | _, _ :: _,        [],          _, h => by cases h

/-- `EnvAgrees` implies pointwise Val.lc of `γ`. -/
theorem EnvAgrees.allLc :
    ∀ {κ Γ γ ρ}, EnvAgrees κ Γ γ ρ → Subst.AllClosed γ
  | _, [],            [],          _, _ => True.intro
  | _, (_, _) :: _,   (_, v) :: γ, _, h => by
      obtain ⟨_, hΓ, hv, _, _⟩ := h
      exact ⟨TyDenote.lc hv, EnvAgrees.allLc hΓ⟩
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

/-- REnv.extendBy s ρ x va = ρ when va is the γ-value for x and ρ reflects γ. -/
theorem EnvAgrees.extendBy_idem {κ Γ γ ρ x s va}
    (hE : EnvAgrees κ Γ γ ρ) (hlk_Γ : Γ.lookup x = some s)
    (hlk_γ : Subst.lookup x γ = some va) : REnv.extendBy s ρ x va = ρ := by
  obtain ⟨v₀, hlk_γ', _, _, hint, hbool⟩ := EnvAgrees.lookup_some hE hlk_Γ
  -- va and v₀ must be equal since both are lookup x γ
  have hveq : va = v₀ := Option.some.inj (hlk_γ.symm.trans hlk_γ')
  subst hveq
  cases s with
  | refine b r =>
    cases b with
    | int  =>
      cases va with
      | iconst n =>
        simp only [REnv.extendBy]
        exact REnv.update_idem_int ρ x n (hint n rfl)
      | bconst _ => simp only [REnv.extendBy]
      | clos _   => simp only [REnv.extendBy]
    | bool =>
      cases va with
      | bconst b =>
        simp only [REnv.extendBy]
        exact REnv.update_idem_bool ρ x b (hbool b rfl)
      | iconst _ => simp only [REnv.extendBy]
      | clos _   => simp only [REnv.extendBy]
  | arrow _ _ => simp [REnv.extendBy]

/-! ## extendBy commutativity and extendBy_fresh -/

/-- `extendBy` at two different variables commutes. -/
private theorem REnv.extendBy_comm (s s' : Ty) (ρ : REnv) (x z : EVar) (va va' : Val)
    (hxz : x ≠ z) :
    REnv.extendBy s (REnv.extendBy s' ρ z va') x va =
    REnv.extendBy s' (REnv.extendBy s ρ x va) z va' := by
  rcases s with (_ | _ | _) | _ <;> rcases s' with (_ | _ | _) | _ <;>
    rcases va with n | bv | _ <;> rcases va' with n' | bv' | _ <;>
    simp only [REnv.extendBy]
  · exact (REnv.update_int_int_comm ρ x z hxz n n').symm
  · exact (REnv.update_bool_bool_comm ρ x z hxz bv bv').symm

/-- Helper: updating ρ at a fresh x (x ∉ r.rawfv, x ∉ r.named, x ≠ nuName)
    does not change Refinement.interp. -/
private theorem Refinement.interp_extendBy_fresh {κ : KEnv} {b : Base} (r : Refinement b)
    (s : Ty) (x : EVar) (va : Val) (ρ : REnv)
    (hx : x ∉ Refinement.rawfv r) (hxn : x ∉ Refinement.named r) (hxν : x ≠ nuName)
    {w : b.interp} :
    Refinement.interp κ r ρ w ↔ Refinement.interp κ r (REnv.extendBy s ρ x va) w := by
  cases r with
  | fmla φ =>
    simp only [Refinement.rawfv, Refinement.named] at hx hxn
    simp only [Refinement.interp]
    rcases s with (_ | _ | _) | _ <;> rcases va with n | bv | _
    all_goals simp only [REnv.extendBy]
    · have hcomm : (ρ.update .int x n).update b nuName w =
                   (ρ.update b nuName w).update .int x n := by
        cases b with
        | int  => exact (REnv.update_int_int_comm ρ nuName x hxν.symm w n).symm
        | bool => exact (REnv.update_int_bool_comm ρ x nuName n w).symm
      rw [hcomm]
      have := Formula.interp_update_fresh_int φ x n (ρ.update b nuName w) hx hxn
      grind
    · have := Formula.interp_update_fresh_bool φ x bv (ρ.update b nuName w) hx hxn
      have hcomm : (ρ.update .bool x bv).update b nuName w =
                   (ρ.update b nuName w).update .bool x bv := by
        cases b with
        | int => rw [REnv.update_int_bool_comm]
        | bool => rw [REnv.update_bool_bool_comm] ; grind
      rw [hcomm]
      assumption
  | kapp kn args =>
    have hargs : ∀ a ∈ args, x ∉ Term.fv a.2 := fun a ha hm =>
      hx (by simp only [Refinement.rawfv, List.mem_flatMap]; exact ⟨a, ha, hm⟩)
    simp only [Refinement.interp]
    rcases s with (_ | _ | _) | _ <;> rcases va with n | bv | _
    all_goals simp only [REnv.extendBy]
    · -- update .int x n
      apply Iff.of_eq; congr 1
      apply List.map_congr_left
      intro a ha
      have hcomm : (ρ.update .int x n).update b nuName w =
                   (ρ.update b nuName w).update .int x n := by
        cases b with
        | int  => exact (REnv.update_int_int_comm ρ nuName x hxν.symm w n).symm
        | bool => exact (REnv.update_int_bool_comm ρ x nuName n w).symm
      rw [hcomm]; congr 1
      exact (Term.interp_update_fresh_int a.2 x n (ρ.update b nuName w) (hargs a ha)).symm
    · -- update .bool x bv
      apply Iff.of_eq; congr 1
      apply List.map_congr_left
      intro a ha
      have hcomm : (ρ.update .bool x bv).update b nuName w =
                   (ρ.update b nuName w).update .bool x bv := by
        cases b with
        | int => rw [REnv.update_int_bool_comm]
        | bool => rw [REnv.update_bool_bool_comm] ; grind
      rw [hcomm]; congr 1
      exact (Term.interp_update_fresh_bool a.2 x bv (ρ.update b nuName w) (hargs a ha)).symm

/-- Combined Iff proved by strong induction on `t.skel`.
    Derives both `extendBy_fresh` and `of_extendBy_fresh` as corollaries. -/
private theorem TyDenote.extendBy_fresh_iff_aux (n : Nat) :
    ∀ (κ : KEnv) (t : Ty) (_ : t.skel ≤ n) (ρ : REnv) (v : Val)
      (s : Ty) (x : EVar) (va : Val)
      (_ : x ∉ t.fv) (_ : x ∉ Ty.named t) (_ : x ≠ nuName),
      TyDenote κ t ρ v ↔ TyDenote κ t (REnv.extendBy s ρ x va) v := by
  induction n with
  | zero =>
    intro κ t hn ρ v s x va hx hxn hxν
    match t with
    | .refine b r =>
      have hx' := Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      cases b <;> simp only [TyDenote] <;> constructor
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mp hp⟩
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mpr hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mp hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mpr hp⟩
    | .arrow _ _ => simp [Ty.skel] at hn
  | succ n ih =>
    intro κ t hn ρ v s x va hx hxn hxν
    match t with
    | .refine b r =>
      have hx' := Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      cases b <;> simp only [TyDenote] <;> constructor
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mp hp⟩
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mpr hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mp hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mpr hp⟩
    | .arrow s' t' =>
      simp only [Ty.skel] at hn
      have hns' : s'.skel ≤ n := by omega
      have hnt' : t'.skel ≤ n := by omega
      simp only [Ty.fv, List.mem_append, not_or] at hx
      simp only [Ty.named, List.mem_append, not_or] at hxn
      simp only [TyDenote]
      constructor
      · -- extendBy_fresh direction: ρ → extendBy s ρ x va
        intro ⟨body, hvclos, hlc, hcl, hLR⟩
        refine ⟨body, hvclos, hlc, hcl, fun va' htd_va' => ?_⟩
        have htd_va'_ρ : TyDenote κ s' ρ va' :=
          (ih κ s' hns' ρ va' s x va hx.1 hxn.1 hxν).mpr htd_va'
        obtain ⟨vr, hbs_vr, htd_vr⟩ := hLR va' htd_va'_ρ
        have hnt'va : (t'.substBV va').skel ≤ n := by rw [Ty.skel_substBV]; exact hnt'
        -- x ∉ (t'.substBV va').fv and named: sorried, follows from x ∉ t'.fv/named
        have hx_t'va : x ∉ (t'.substBV va').fv := by
          grind [Ty.fv_substBV_not_mem]
        have hxn_t'va : x ∉ Ty.named (t'.substBV va') := by
          grind [Ty.named_substBV_not_mem]
        exact ⟨vr, hbs_vr,
          (ih κ (t'.substBV va') hnt'va ρ vr s x va hx_t'va hxn_t'va hxν).mp htd_vr⟩
      · -- of_extendBy_fresh direction: extendBy s ρ x va → ρ
        intro ⟨body, hvclos, hlc, hcl, hLR⟩
        refine ⟨body, hvclos, hlc, hcl, fun va' htd_va' => ?_⟩
        have htd_va'_ext : TyDenote κ s' (REnv.extendBy s ρ x va) va' :=
          (ih κ s' hns' ρ va' s x va hx.1 hxn.1 hxν).mp htd_va'
        obtain ⟨vr, hbs_vr, htd_vr⟩ := hLR va' htd_va'_ext
        have hnt'va : (t'.substBV va').skel ≤ n := by rw [Ty.skel_substBV]; exact hnt'
        have hx_t'va : x ∉ (t'.substBV va').fv := by
          grind [Ty.fv_substBV_not_mem]
        have hxn_t'va : x ∉ Ty.named (t'.substBV va') := by
          grind [Ty.named_substBV_not_mem]
        exact ⟨vr, hbs_vr,
          (ih κ (t'.substBV va') hnt'va ρ vr s x va hx_t'va hxn_t'va hxν).mpr htd_vr⟩

/-- TyDenote is monotone under extension at a variable x that doesn't appear
    freely in t or as a named binder in t's formulas. -/
theorem TyDenote.extendBy_fresh {κ : KEnv} {t : Ty} {ρ : REnv} {v : Val}
    (s : Ty) (x : EVar) (va : Val)
    (hx : x ∉ t.fv) (hxn : x ∉ Ty.named t) (hxν : x ≠ nuName)
    (h : TyDenote κ t ρ v) :
    TyDenote κ t (REnv.extendBy s ρ x va) v := by
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
      exact (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mp hp
    | bool =>
      simp only [TyDenote] at h ⊢
      obtain ⟨bv, hvb, hp⟩ := h
      refine ⟨bv, hvb, ?_⟩
      have hx' : x ∉ Refinement.rawfv r :=
        Refinement.fv_filter_of_ne_nu r x hx hxν
      have hxn' : x ∉ Refinement.named r := by simpa [Ty.named] using hxn
      exact (Refinement.interp_extendBy_fresh r s x va ρ hx' hxn' hxν).mp hp
  | arrow s' t' =>
    exact (TyDenote.extendBy_fresh_iff_aux (Ty.arrow s' t').skel κ (.arrow s' t') (by omega) ρ v s x va hx hxn hxν).mp h

/-- Reverse direction: TyDenote under extendBy at fresh x implies TyDenote at ρ. -/
theorem TyDenote.of_extendBy_fresh {κ : KEnv} {t : Ty} {ρ : REnv} {v : Val}
    (s : Ty) (x : EVar) (va : Val)
    (hx : x ∉ t.fv) (hxn : x ∉ Ty.named t) (hxν : x ≠ nuName)
    (h : TyDenote κ t (REnv.extendBy s ρ x va) v) :
    TyDenote κ t ρ v :=
  (TyDenote.extendBy_fresh_iff_aux t.skel κ t (by omega) ρ v s x va hx hxn hxν).mpr h

private theorem TyDenote.substBV_iff_aux (n : Nat) :
      ∀ (j : Nat) (κ : KEnv) (t : Ty) (_ : t.skel ≤ n) (s : Ty) (x : EVar) (ρ : REnv)
        (va : Val) (v : Val)
        (_ : x ∉ t.fv) (_ : x ∉ Ty.named t) (_ : x ≠ nuName)
        (_ : Ty.WFBVarCtx (List.replicate j none ++ [s.optBase]) t)
        (_ : TyDenote κ s ρ va),
        TyDenote κ (t.substBV_aux j va) ρ v ↔
        TyDenote κ (t.openVar j x) (REnv.extendBy s ρ x va) v := by
  induction n with
  | zero =>
    intro j κ t hsk
    cases t <;> simp at hsk
    rename_i b r
    intro s x ρ va v hxf hxn hxnn hwfb htd
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
          simp only [Ty.substBV_aux, REnv.extendBy, Ty.openVar]
          -- inner `.bool` opening is a no-op (WF: only `.int` BVars at this level)
          rw [Refinement.openBVar_noop (r.openBVar .int j x) .bool j x (by
                intro hbv
                rw [Refinement.hasBVar_openBVar_other r .bool .int j j x (Or.inl (by decide))] at hbv
                exact absurd (hwfb .bool j hbv) (by simp))]
          cases b <;> simp only [TyDenote] <;>
            exact ⟨fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .int j n x ρ hx_rfv hxn hxnn).mp h⟩,
                   fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .int j n x ρ hx_rfv hxn hxnn).mpr h⟩⟩
        | bool => simp [TyDenote] at htd
    | bconst bv =>
      cases s with
      | arrow s_d s_c => simp [TyDenote] at htd
      | refine sb r' =>
        cases sb with
        | bool =>
          simp only [Ty.optBase] at hwfb
          simp only [Ty.substBV_aux, REnv.extendBy, Ty.openVar]
          rw [Refinement.openBVar_noop r .int j x (by
                intro hbv; exact absurd (hwfb .int j hbv) (by simp))]
          cases b <;> simp only [TyDenote] <;>
            exact ⟨fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .bool j bv x ρ hx_rfv hxn hxnn).mp h⟩,
                   fun ⟨m, hm, h⟩ =>
                     ⟨m, hm, (Refinement.interp_substBV κ r .bool j bv x ρ hx_rfv hxn hxnn).mpr h⟩⟩
        | int => simp [TyDenote] at htd
    | clos body =>
      simp only [Ty.substBV_aux, REnv.extendBy, Ty.openVar]
      cases s with
      | arrow s_d s_c =>
        simp only [Ty.optBase] at hwfb
        rw [Refinement.openBVar_noop r .int j x (by
              intro hbv; exact absurd (hwfb .int j hbv) (by simp)),
            Refinement.openBVar_noop r .bool j x (by
              intro hbv; exact absurd (hwfb .bool j hbv) (by simp))]
      | refine sb r' =>
        cases sb with
        | int  => simp only [TyDenote] at htd; obtain ⟨_, h, _⟩ := htd; simp at h
        | bool => simp only [TyDenote] at htd; obtain ⟨_, h, _⟩ := htd; simp at h
  | succ n ih =>
    intro j κ t hsk s x ρ va v hxf hxn hxν hwfb htd
    -- If t.skel ≤ n, delegate directly to IH
    by_cases hn : t.skel ≤ n
    · exact ih j κ t hn s x ρ va v hxf hxn hxν hwfb htd
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
        -- Derives compat from TyDenote κ (s'.substBV_aux j va) ρ va' and builds WFBVarCtx
        have mk_wf_cod : ∀ va',
            TyDenote κ (s'.substBV_aux j va) ρ va' →
            Ty.WFBVarCtx (List.replicate (j+1) none ++ [s.optBase]) (t'.substBV_aux 0 va') := by
          intro va' htd_va'_ρ
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
                rw [hr'] at htd_va'_ρ; simp only [TyDenote] at htd_va'_ρ
                exact ⟨_, htd_va'_ρ.choose_spec.1⟩
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
                rw [hr'] at htd_va'_ρ; simp only [TyDenote] at htd_va'_ρ
                exact ⟨_, htd_va'_ρ.choose_spec.1⟩
          have h := Ty.WFBVarCtx_substBV_aux_prefix t' [] s'.optBase
            (List.replicate j none ++ [s.optBase]) va'
            (by simpa using hwfb_t') hci' hcb'
          simpa [List.replicate_succ] using h
        constructor
        · -- LHS (substBV/ρ) → RHS (openVar/extendBy)
          rintro ⟨body, rfl, hlc, hcl, hLR⟩
          refine ⟨body, rfl, hlc, hcl, fun va' htd_va' => ?_⟩
          simp [Ty.named] at hxn
          have htd_va'_ρ : TyDenote κ (s'.substBV_aux j va) ρ va' :=
            (ih j κ s' hns' s x ρ va va' hxf.1 hxn.1 hxν hwfb_s' htd).mpr htd_va'
          obtain ⟨vr, hbs, htd_vr⟩ := hLR va' htd_va'_ρ
          refine ⟨vr, hbs, ?_⟩
          -- htd_vr : TyDenote κ ((t'.substBV_aux (j+1) va).substBV va') ρ vr
          simp only [Ty.substBV] at htd_vr ⊢
          -- Now htd_vr uses substBV_aux 0; rewrite via comm
          rw [Ty.substBV_aux_comm t' va (j+1) va' 0 (by omega)] at htd_vr
          rw [← Ty.openVar_substBV_aux_comm t' (j+1) x va' 0 (by omega)]
          exact (ih (j+1) κ (t'.substBV_aux 0 va') (by rw [←Ty.substBV] ; rw [Ty.skel_substBV]; exact hnt')
                    s x ρ va vr
                    (Ty.fv_substBV_not_mem t' x va' hxf.2)
                    (Ty.named_substBV_not_mem t' x va' hxn.2)
                    hxν (mk_wf_cod va' htd_va'_ρ) htd).mp htd_vr
        · -- RHS (openVar/extendBy) → LHS (substBV/ρ)
          rintro ⟨body, rfl, hlc, hcl, hLR⟩
          refine ⟨body, rfl, hlc, hcl, fun va' htd_va'_ρ => ?_⟩
          simp [Ty.named] at hxn
          have htd_va' : TyDenote κ (s'.openVar j x) (REnv.extendBy s ρ x va) va' :=
            (ih j κ s' hns' s x ρ va va' hxf.1 hxn.1 hxν hwfb_s' htd).mp htd_va'_ρ
          obtain ⟨vr, hbs, htd_vr⟩ := hLR va' htd_va'
          refine ⟨vr, hbs, ?_⟩
          -- htd_vr : TyDenote κ ((t'.openVar (j+1) x).substBV va') (extendBy s ρ x va) vr
          simp only [Ty.substBV] at htd_vr ⊢
          rw [← Ty.openVar_substBV_aux_comm t' (j+1) x va' 0 (by omega)] at htd_vr
          have htd_vr' := (ih (j+1) κ (t'.substBV_aux 0 va') (by rw [←Ty.substBV] ; rw [Ty.skel_substBV]; exact hnt')
                    s x ρ va vr
                    (Ty.fv_substBV_not_mem t' x va' hxf.2)
                    (Ty.named_substBV_not_mem t' x va' hxn.2)
                    hxν (mk_wf_cod va' htd_va'_ρ) htd).mpr htd_vr
          rw [Ty.substBV_aux_comm]
            <;> grind

/-- `substBV va` in TyDenote corresponds to `openVar 0 x` with `extendBy s ρ x va`,
    when x is fresh for t, va is compatible with s (TyDenote κ s ρ va), and t is
    well-formed (WFBVarCtx [s.optBase] t) so that only the correct-base BVars appear. -/
theorem TyDenote.substBV_iff (κ : KEnv) (t : Ty) (s : Ty) (x : EVar) (ρ : REnv)
    (va : Val) (v : Val)
    (hx_fv : x ∉ t.fv) (hx_named : x ∉ Ty.named t) (hxν : x ≠ nuName)
    (hWF : Ty.WFBVarCtx [s.optBase] t)
    (hcompat : TyDenote κ s ρ va) :
    TyDenote κ (t.substBV va) ρ v ↔
    TyDenote κ (t.openVar 0 x) (REnv.extendBy s ρ x va) v := by
  apply TyDenote.substBV_iff_aux t.skel
  · omega
  · assumption
  · assumption
  · assumption
  · simp ; assumption
  · assumption
/-- Helper: extendBy at x ≠ y does not change ρ.ints y or ρ.bools y. -/
private theorem REnv.extendBy_ints_other (s : Ty) (ρ : REnv) (x y : EVar) (va : Val)
    (hxy : x ≠ y) : (REnv.extendBy s ρ x va).ints y = ρ.ints y := by
  rcases s with (_ | _ | _) | _ <;> rcases va with n | bv | _
  all_goals simp only [REnv.extendBy, REnv.update]
  simp [beq_eq_false_iff_ne.mpr hxy]

private theorem REnv.extendBy_bools_other (s : Ty) (ρ : REnv) (x y : EVar) (va : Val)
    (hxy : x ≠ y) : (REnv.extendBy s ρ x va).bools y = ρ.bools y := by
  rcases s with (_ | _ | _) | _ <;> rcases va with n | bv | _
  all_goals simp only [REnv.extendBy, REnv.update]
  simp [beq_eq_false_iff_ne.mpr hxy]

theorem EnvAgrees.extendBy_fresh {κ Γ γ ρ} (hE : EnvAgrees κ Γ γ ρ)
    (s : Ty) (x : EVar) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) (hx_named : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName) :
    EnvAgrees κ Γ γ (REnv.extendBy s ρ x va) := by
  induction Γ generalizing γ with
  | nil =>
    cases γ with
    | nil  => exact True.intro
    | cons _ _ => cases hE
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    cases γ with
    | nil => cases hE
    | cons hd' tl' =>
      obtain ⟨_, v⟩ := hd'
      obtain ⟨hhd, htl, htd, hint, hbool⟩ := hE
      simp only [TEnv.dom, List.mem_cons, not_or] at hx_dom
      simp only [TEnv.tyFv, List.mem_append, not_or] at hx_fv
      simp only [TEnv.tyNamed, List.mem_append, not_or] at hx_named
      have hxy : x ≠ y := hx_dom.1
      refine ⟨hhd, ih htl hx_dom.2 hx_fv.2 hx_named.2, ?_, ?_, ?_⟩
      · exact TyDenote.extendBy_fresh s x va hx_fv.1 hx_named.1 hxν htd
      · intro n hn
        rw [REnv.extendBy_ints_other s ρ x y va hxy]
        exact hint n hn
      · intro b hb
        rw [REnv.extendBy_bools_other s ρ x y va hxy]
        exact hbool b hb


/-- Extend `EnvAgrees` by prepending a fresh `(x, va)` binding.
    Requires:
    - x fresh from Γ's domain (so existing bindings are unaffected by extendBy)
    - TyDenote κ s₁ (extendBy s₁ ρ x va) va (the new binding is in its own LR)
    - EnvAgrees κ Γ γ ρ is preserved under extendBy at fresh x -/
theorem EnvAgrees.extend {κ Γ γ ρ} (hE : EnvAgrees κ Γ γ ρ)
    (x : EVar) (s₁ : Ty) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (_ : x ∉ Subst.dom γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) (hx_named : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName)
    (htd : TyDenote κ s₁ (REnv.extendBy s₁ ρ x va) va) :
    EnvAgrees κ ((x, s₁) :: Γ) ((x, va) :: γ) (REnv.extendBy s₁ ρ x va) := by
  refine ⟨rfl, EnvAgrees.extendBy_fresh hE s₁ x va hx_dom hx_fv hx_named hxν, htd, ?_, ?_⟩

  · -- hint: ∀ n, va = .iconst n → (extendBy s₁ ρ x va).ints x = n
    intro n hn; subst hn
    cases s₁ with
    | arrow _ _ =>
      simp only [TyDenote] at htd; obtain ⟨body', hvc, _⟩ := htd; exact absurd hvc (by simp)
    | refine b r =>
      cases b with
      | bool =>
        simp only [TyDenote] at htd; obtain ⟨bv, hvb, _⟩ := htd; exact absurd hvb (by simp)
      | int =>
        simp only [TyDenote] at htd; obtain ⟨n', hvn, _⟩ := htd
        simp only [Val.iconst.injEq] at hvn; subst hvn
        simp [REnv.extendBy, REnv.update]
  · -- hbool: ∀ b, va = .bconst b → (extendBy s₁ ρ x va).bools x = b
    intro b hb; subst hb
    cases s₁ with
    | arrow _ _ =>
      simp only [TyDenote] at htd; obtain ⟨body', hvc, _⟩ := htd; exact absurd hvc (by simp)
    | refine base r =>
      cases base with
      | int =>
        simp only [TyDenote] at htd; obtain ⟨n', hvn, _⟩ := htd; exact absurd hvn (by simp)
      | bool =>
        simp only [TyDenote] at htd; obtain ⟨bv, hvb, _⟩ := htd
        simp only [Val.bconst.injEq] at hvb; subst hvb
        simp [REnv.extendBy, REnv.update]

/-- The domain of γ equals the domain of Γ under EnvAgrees. -/
theorem EnvAgrees.dom_eq :
    ∀ {κ Γ γ ρ}, EnvAgrees κ Γ γ ρ → TEnv.dom Γ = Subst.dom γ
  | _, [],            [],          _, _ => rfl
  | _, (x, _) :: Γ', (y, _) :: γ', _, h => by
      obtain ⟨hxy, hrest, _⟩ := h; subst hxy
      simp [TEnv.dom, Subst.dom, EnvAgrees.dom_eq hrest]
  | _, [],            _ :: _,      _, h => by cases h
  | _, _ :: _,        [],          _, h => by cases h

/-! ## T1 — Subtyping is semantic inclusion of denotations -/

private theorem Subtyp.optBase_eq {κ Γ s t} (h : Subtyp κ Γ s t) : s.optBase = t.optBase := by
  cases h with
  | refine => rfl
  | arrow => simp [Ty.optBase]

/-- ModelsEnv is preserved when extending ρ at z fresh from Γ. -/
private theorem ModelsEnv.extendBy_fresh_aux {κ : KEnv} {Γ : TEnv} {ρ : REnv}
    (hm : ModelsEnv κ ρ Γ) (s : Ty) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_named : z ∉ TEnv.tyNamed Γ)
    (hzν : z ≠ nuName) :
    ModelsEnv κ (REnv.extendBy s ρ z va) Γ := by
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
      obtain ⟨hhead, htail⟩ := hm
      refine ⟨?_, ih htail hz_dom.2 hz_fv.2 hz_named.2⟩
      have hzy : z ≠ y := hz_dom.1
      have hz_rfv : z ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r z hz_fv.1 hzν
      have hz_rnamed : z ∉ Refinement.named r := by simpa [Ty.named] using hz_named.1
      have hget : REnv.get b (REnv.extendBy s ρ z va) y = REnv.get b ρ y := by
        cases b with
        | int  => exact REnv.extendBy_ints_other s ρ z y va hzy
        | bool => exact REnv.extendBy_bools_other s ρ z y va hzy
      rw [hget]
      exact (Refinement.interp_extendBy_fresh r s z va ρ hz_rfv hz_rnamed hzν).mp hhead

/-- Build ModelsEnv after prepending a fresh binding (z, s₂). -/
private theorem ModelsEnv.extendBy_cons {κ : KEnv} {Γ : TEnv} {ρ : REnv}
    (hm : ModelsEnv κ ρ Γ) (s₂ : Ty) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_named : z ∉ TEnv.tyNamed Γ)
    (hz_s2fv : z ∉ s₂.fv)
    (hz_s2named : z ∉ Ty.named s₂)
    (hzν : z ≠ nuName)
    (htd_va : TyDenote κ s₂ ρ va) :
    ModelsEnv κ (REnv.extendBy s₂ ρ z va) ((z, s₂) :: Γ) := by
  have htail := ModelsEnv.extendBy_fresh_aux hm s₂ z va hz_dom hz_fv hz_named hzν
  cases s₂ with
  | arrow s' t' => simp only [ModelsEnv]; exact htail
  | refine b r =>
    simp only [ModelsEnv]
    refine ⟨?_, htail⟩
    have hz_rfv : z ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r z hz_s2fv hzν
    have hz_rnamed : z ∉ Refinement.named r := by simpa [Ty.named] using hz_s2named
    cases b with
    | int =>
      simp only [TyDenote] at htd_va
      obtain ⟨n, hvn, hp⟩ := htd_va; subst hvn
      simp only [REnv.extendBy, REnv.get, REnv.update, beq_self_eq_true, ↓reduceIte]
      exact (Refinement.interp_extendBy_fresh r (.refine .int r) z (.iconst n) ρ
              hz_rfv hz_rnamed hzν).mp hp
    | bool =>
      simp only [TyDenote] at htd_va
      obtain ⟨bv, hvb, hp⟩ := htd_va; subst hvb
      simp only [REnv.extendBy, REnv.get, REnv.update, beq_self_eq_true, ↓reduceIte]
      exact (Refinement.interp_extendBy_fresh r (.refine .bool r) z (.bconst bv) ρ
              hz_rfv hz_rnamed hzν).mp hp

theorem subtyp_sound {κ Γ s t} (hsub : Subtyp κ Γ s t)
    (hWF_s : Ty.WFBVars s) (hWF_t : Ty.WFBVars t) :
    ∀ {ρ}, ModelsEnv κ ρ Γ → ∀ {v}, TyDenote κ s ρ v → TyDenote κ t ρ v := by
  induction hsub with
  | refine hent =>
      rename_i b r₁ r₂
      intro ρ hΓ v hs
      cases b with
      | int =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨n, hvn, hp₁⟩ := hs
        exact ⟨n, hvn, hent ρ hΓ n hp₁⟩
      | bool =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨bv, hvb, hp₁⟩ := hs
        exact ⟨bv, hvb, hent ρ hΓ bv hp₁⟩
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
    intro ρ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨body, hvc, hlc, hcl, hLR⟩ := htd
    refine ⟨body, hvc, hlc, hcl, fun va htd_va => ?_⟩
    -- Domain conversion (contravariant): s₂ <: s₁ so s₂-typed va is also s₁-typed
    have htd_va_s1 : TyDenote κ s₁ ρ va := ih_hdom hWF_s2 hWF_s1 hm htd_va
    -- Apply the function body at s₁-typed va
    obtain ⟨vr, hbs, htd_vr_t1⟩ := hLR va htd_va_s1
    refine ⟨vr, hbs, ?_⟩
    -- Use x directly from the constructor (no fresh pick needed)
    have hWF_t1x : Ty.WFBVars (t₁.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₁ [] s₂.optBase x hWF_st1'
    have hWF_t2x : Ty.WFBVars (t₂.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₂ [] s₂.optBase x hWF_t2
    -- Convert t₁.substBV va ↔ t₁.openVar 0 x under extendBy s₂ ρ x va
    rw [TyDenote.substBV_iff κ t₁ s₂ x ρ va vr hx_t1fv hx_t1named hxν hWF_st1' htd_va]
      at htd_vr_t1
    -- Build extended model for ((x, s₂) :: Γ')
    have hm_ext : ModelsEnv κ (REnv.extendBy s₂ ρ x va) ((x, s₂) :: Γ') :=
      ModelsEnv.extendBy_cons hm s₂ x va hx_Γdom hx_Γfv hx_Γnamed hx_s2fv hx_s2named hxν htd_va
    -- Apply codomain IH at x
    have htd_vr_t2 : TyDenote κ (t₂.openVar 0 x) (REnv.extendBy s₂ ρ x va) vr :=
      ih_hcodom hWF_t1x hWF_t2x hm_ext htd_vr_t1
    -- Convert back: t₂.openVar 0 x ↔ t₂.substBV va
    exact (TyDenote.substBV_iff κ t₂ s₂ x ρ va vr hx_t2fv hx_t2named hxν hWF_t2 htd_va).mpr
      htd_vr_t2

/-! ## T2 — Fundamental Lemma -/

theorem hastype_fundamental {κ Γ e t} (h : Hastype κ Γ e t) :
    ∀ {γ ρ}, EnvAgrees κ Γ γ ρ →
    ∃ v, BigStep (Exp.substEnv γ e) v ∧ TyDenote κ t ρ v := by
  induction h with
  | var hlk _ =>
      rename_i Γ x t hwf
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
                obtain ⟨n, hvn, _⟩ := hv
                simp only [self, TyDenote]
                refine ⟨n, hvn, ?_⟩
                simp [Refinement.interp, Formula.interp, Term.interp,
                      REnv.get, hint n hvn]
            | bool =>
                simp only [TyDenote] at hv
                obtain ⟨bv, hvb, _⟩ := hv
                simp only [self, TyDenote]
                refine ⟨bv, hvb, ?_⟩
                simp [Refinement.interp, Formula.interp, Term.interp,
                      REnv.get, hbool bv hvb]
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
  | ann _ _ =>
      rename_i hht _ ih
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      refine ⟨v, ?_, hv⟩
      rw [Exp.substEnv_ann]
      exact BigStep.ann hbs
  | sub hhs hsub hwf_t ih =>
      intro γ ρ hE
      obtain ⟨v, hbs, hv⟩ := ih hE
      exact ⟨v, hbs, subtyp_sound hsub hhs.wf_bvars hwf_t (EnvAgrees.toModelsEnv hE) hv⟩
  | add_var hlk₁ hlk₂ hxν hyν =>
      rename_i x y r₁ r₂
      intro γ ρ hE
      obtain ⟨v₁, hlkγ₁, hv₁, hcl₁, hint₁, _⟩ := EnvAgrees.lookup_some hE hlk₁
      simp only [TyDenote] at hv₁; obtain ⟨n₁, hv₁eq, _⟩ := hv₁; subst hv₁eq
      obtain ⟨v₂, hlkγ₂, hv₂, hcl₂, hint₂, _⟩ := EnvAgrees.lookup_some hE hlk₂
      simp only [TyDenote] at hv₂; obtain ⟨n₂, hv₂eq, _⟩ := hv₂; subst hv₂eq
      have hγcl := EnvAgrees.allClosed hE
      have hx := Exp.substEnv_var_lookup x γ (.iconst n₁) hlkγ₁ hcl₁ hγcl
      have hy := Exp.substEnv_var_lookup y γ (.iconst n₂) hlkγ₂ hcl₂ hγcl
      simp only [Val.toExp] at hx hy
      have hρx : ρ.ints x = n₁ := hint₁ n₁ rfl
      have hρy : ρ.ints y = n₂ := hint₂ n₂ rfl
      refine ⟨.iconst (n₁ + n₂), ?_, ?_⟩
      · rw [Exp.substEnv_add, hx, hy]; exact BigStep.add BigStep.iconst BigStep.iconst
      · simp only [TyDenote]; refine ⟨n₁ + n₂, rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp, REnv.get]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        have hνy : (nuName == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hyν)
        simp [hνx, hνy, hρx, hρy]
  | leq_var hlk₁ hlk₂ hxν hyν =>
      rename_i x y r₁ r₂
      intro γ ρ hE
      obtain ⟨v₁, hlkγ₁, hv₁, hcl₁, hint₁, _⟩ := EnvAgrees.lookup_some hE hlk₁
      simp only [TyDenote] at hv₁; obtain ⟨n₁, hv₁eq, _⟩ := hv₁; subst hv₁eq
      obtain ⟨v₂, hlkγ₂, hv₂, hcl₂, hint₂, _⟩ := EnvAgrees.lookup_some hE hlk₂
      simp only [TyDenote] at hv₂; obtain ⟨n₂, hv₂eq, _⟩ := hv₂; subst hv₂eq
      have hγcl := EnvAgrees.allClosed hE
      have hx := Exp.substEnv_var_lookup x γ (.iconst n₁) hlkγ₁ hcl₁ hγcl
      have hy := Exp.substEnv_var_lookup y γ (.iconst n₂) hlkγ₂ hcl₂ hγcl
      simp only [Val.toExp] at hx hy
      have hρx : ρ.ints x = n₁ := hint₁ n₁ rfl
      have hρy : ρ.ints y = n₂ := hint₂ n₂ rfl
      refine ⟨.bconst (decide (n₁ ≤ n₂)), ?_, ?_⟩
      · rw [Exp.substEnv_leq, hx, hy]; exact BigStep.leq BigStep.iconst BigStep.iconst
      · simp only [TyDenote]; refine ⟨decide (n₁ ≤ n₂), rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp, REnv.get]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        have hνy : (nuName == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hyν)
        simp only [hρx, hρy]
        constructor
        · intro h; exact decide_eq_true_iff.mp h
        · intro h; exact decide_eq_true_iff.mpr h
  | not_var hlk hxν =>
      rename_i x r
      intro γ ρ hE
      obtain ⟨v₁, hlkγ₁, hv₁, hcl₁, _, hbool₁⟩ := EnvAgrees.lookup_some hE hlk
      simp only [TyDenote] at hv₁; obtain ⟨b, hv₁eq, _⟩ := hv₁; subst hv₁eq
      have hγcl := EnvAgrees.allClosed hE
      have hx := Exp.substEnv_var_lookup x γ (.bconst b) hlkγ₁ hcl₁ hγcl
      simp only [Val.toExp] at hx
      have hρx : ρ.bools x = b := hbool₁ b rfl
      refine ⟨.bconst (!b), ?_, ?_⟩
      · rw [Exp.substEnv_not, hx]; exact BigStep.not_ BigStep.bconst
      · simp only [TyDenote]; refine ⟨!b, rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp, REnv.get]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        simp [hνx, hρx]
  | and_var hlkx hlky hxν hyν =>
      rename_i x y rx ry
      intro γ ρ hE
      obtain ⟨vx, hlkγx, hvx, hclx, _, hboolx⟩ := EnvAgrees.lookup_some hE hlkx
      simp only [TyDenote] at hvx; obtain ⟨bx, hvxeq, _⟩ := hvx; subst hvxeq
      obtain ⟨vy, hlkγy, hvy, hcly, _, hbooly⟩ := EnvAgrees.lookup_some hE hlky
      simp only [TyDenote] at hvy; obtain ⟨by_, hvyeq, _⟩ := hvy; subst hvyeq
      have hγcl := EnvAgrees.allClosed hE
      have hxx := Exp.substEnv_var_lookup x γ (.bconst bx) hlkγx hclx hγcl
      have hyy := Exp.substEnv_var_lookup y γ (.bconst by_) hlkγy hcly hγcl
      simp only [Val.toExp] at hxx hyy
      have hρx : ρ.bools x = bx := hboolx bx rfl
      have hρy : ρ.bools y = by_ := hbooly by_ rfl
      refine ⟨.bconst (bx && by_), ?_, ?_⟩
      · rw [Exp.substEnv_and, hxx, hyy]; exact BigStep.and_ BigStep.bconst BigStep.bconst
      · simp only [TyDenote]; refine ⟨bx && by_, rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp, REnv.get]
        have hνx : (nuName == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxν)
        have hνy : (nuName == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hyν)
        simp [hνx, hνy, hρx, hρy]
  | lam hwf_arr hfresh ih =>
      rename_i Γ' body s₁ s₂ x ih_fund
      intro γ ρ hE
      rw [Exp.substEnv_lam]
      refine ⟨.clos (Exp.substEnv γ body), BigStep.lam, ?_⟩
      simp only [TyDenote]
      refine ⟨Exp.substEnv γ body, rfl, ?_, ?_, ?_⟩
      · -- Val.lc
        simp only [Val.lc]
        exact Exp.substEnv_lc_at γ body 1 (EnvAgrees.allLc hE) (Hastype.lam hwf_arr hfresh ih).lc_at
      · -- Val.closed
        simp only [Val.closed, Val.fv]
        apply Exp.substEnv_fv_nil _ _ (EnvAgrees.allClosed hE)
        intro z hz
        obtain ⟨t', hzΓ⟩ := (Hastype.lam hwf_arr hfresh ih).fv_subset z (by simpa [Exp.fv] using hz)
        rw [← EnvAgrees.dom_eq hE]
        exact mem_TEnv_dom hzΓ
      · -- LR: for any va : s₁, produce vr evaluating body and in s₂.substBV va
        intro va htd_va
        -- x is the witness from the constructor; extract freshness facts
        simp [List.mem_append, not_or] at hfresh
        obtain ⟨hxΓ, hxΓfv, hxΓnamed, hxbody, hxs₁, hxs₂, hxs₁n, hxs₂n, hxν⟩ := hfresh
        have hγlc  := EnvAgrees.allLc hE
        -- x ∉ Subst.dom γ follows from x ∉ TEnv.dom Γ' via EnvAgrees.dom_eq
        have hxγ : x ∉ Subst.dom γ := (EnvAgrees.dom_eq hE) ▸ hxΓ
        have htd_va_x : TyDenote κ s₁ (REnv.extendBy s₁ ρ x va) va :=
          TyDenote.extendBy_fresh s₁ x va hxs₁ hxs₁n hxν htd_va
        have hEx : EnvAgrees κ ((x, s₁) :: Γ') ((x, va) :: γ) (REnv.extendBy s₁ ρ x va) :=
          EnvAgrees.extend hE x s₁ va hxΓ hxγ hxΓfv hxΓnamed hxν htd_va_x
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_fund hEx
        rw [Exp.substEnv_cons_openVar body γ va x hxγ hγlc hxbody (TyDenote.closed htd_va)] at hbs_vr
        have hWF_s₂ : Ty.WFBVarCtx [s₁.optBase] s₂ := hwf_arr.2
        exact ⟨vr, hbs_vr,
          (TyDenote.substBV_iff κ s₂ s₁ x ρ va vr hxs₂ hxs₂n hxν hWF_s₂ htd_va).mpr htd_vr⟩
  | app h_fn h_arg hyfv hynamed hyν ih_fn ih_arg =>
      rename_i e₁ y s t
      intro γ ρ hE
      -- Evaluate the function
      obtain ⟨v_fn, hbs_fn, htd_fn⟩ := ih_fn hE
      simp only [TyDenote] at htd_fn
      obtain ⟨body, hvclos, hlc_clos, hcl_clos, hLR⟩ := htd_fn
      subst hvclos
      -- Evaluate the argument
      obtain ⟨va, hbs_arg, htd_arg⟩ := ih_arg hE
      -- Apply LR directly with va (substBV approach: no fresh z needed)
      obtain ⟨vr, hbs_body, htd_vr⟩ := hLR va htd_arg
      -- htd_vr : TyDenote κ (t.substBV va) ρ vr
      -- Convert to TyDenote κ (t.openVar 0 y) ρ vr using substBV_iff + extendBy_idem
      -- First, prove extendBy s ρ y va = ρ
      have hext : REnv.extendBy s ρ y va = ρ := by
        obtain ⟨s_raw, hlky_raw⟩ := h_arg.fvar_lookup
        obtain ⟨v_raw, hlkγy, _, hcl_raw, hint_raw, hbool_raw⟩ := EnvAgrees.lookup_some hE hlky_raw
        have hγcl := EnvAgrees.allClosed hE
        have hsubst_y := Exp.substEnv_var_lookup y γ v_raw hlkγy hcl_raw hγcl
        have hbs_raw : BigStep v_raw.toExp v_raw := by
          cases v_raw with
          | iconst _ => exact BigStep.iconst
          | bconst _ => exact BigStep.bconst
          | clos body' => exact BigStep.lam
        rw [hsubst_y] at hbs_arg
        have hva_eq : va = v_raw := BigStep.det hbs_arg hbs_raw
        subst hva_eq
        cases s with
        | arrow _ _ => simp [REnv.extendBy]
        | refine b r =>
          cases b with
          | int =>
            simp only [TyDenote] at htd_arg
            obtain ⟨n, hveq, _⟩ := htd_arg
            subst hveq
            simp only [REnv.extendBy]
            exact REnv.update_idem_int ρ y n (hint_raw n rfl)
          | bool =>
            simp only [TyDenote] at htd_arg
            obtain ⟨b, hveq, _⟩ := htd_arg
            subst hveq
            simp only [REnv.extendBy]
            exact REnv.update_idem_bool ρ y b (hbool_raw b rfl)
      -- Use substBV_iff (→ direction) with x = y, then rewrite using hext
      have hWF_t : Ty.WFBVarCtx [s.optBase] t := h_fn.wf_bvars.2
      have htd_vr_y : TyDenote κ (t.openVar 0 y) ρ vr := by
        rw [← hext]
        exact (TyDenote.substBV_iff κ t s y ρ va vr hyfv hynamed hyν hWF_t htd_arg).mp htd_vr
      refine ⟨vr, ?_, htd_vr_y⟩
      rw [Exp.substEnv_app]
      exact BigStep.app hbs_fn hbs_arg hbs_body
  | @letin Γ' e₁ e₂ s' t' x hwfbv hht xf hhto ih₁ ih₂ =>
      intro γ ρ hE
      -- Evaluate e_let
      obtain ⟨v₁, hbs₁, htd₁⟩ := ih₁ hE
      have hγlc := EnvAgrees.allLc hE
      -- x is the constructor's witness; extract freshness from h₁
      simp [List.mem_append, not_or] at xf
      obtain ⟨hxΓ, hxΓfv, hxΓnamed, hxbody, hxs, hxt, hxsn, hxtn, hxν⟩ := xf
      have hxγ : x ∉ Subst.dom γ := by grind [EnvAgrees.dom_eq]--(EnvAgrees.dom_eq hE) ▸ hxΓ
      -- TyDenote for v₁ under extended ρ at x
      have htd₁_x : TyDenote κ s' (REnv.extendBy s' ρ x v₁) v₁ :=
        TyDenote.extendBy_fresh s' x v₁ hxs hxsn hxν htd₁
      -- Extended EnvAgrees at x
      have hEx : EnvAgrees κ ((x, s') :: Γ') ((x, v₁) :: γ) (REnv.extendBy s' ρ x v₁) :=
        EnvAgrees.extend hE x s' v₁ hxΓ hxγ hxΓfv hxΓnamed hxν htd₁_x
      -- Apply IH₂ directly (no fresh pick needed)
      obtain ⟨vr, hbs₂, htd_vr⟩ := ih₂ hEx
      -- Rewrite BigStep: substEnv ((x,v₁)::γ) (body.openVar 0 x) = openVal 0 v₁ (substEnv γ body)
      rw [Exp.substEnv_cons_openVar _ γ v₁ x hxγ hγlc hxbody (TyDenote.closed htd₁)] at hbs₂
      -- Recover TyDenote κ t ρ vr from TyDenote κ t (extendBy s ρ x v₁) vr
      have htd_vr_ρ : TyDenote κ t' ρ vr :=
        TyDenote.of_extendBy_fresh s' x v₁ hxt hxtn hxν htd_vr
      rw [Exp.substEnv_letin]
      exact ⟨vr, BigStep.letin hbs₁ hbs₂, htd_vr_ρ⟩
  | ite hlk hxν hfresh _ h₁ h₂ ih_e₁ ih_e₂ =>
      rename_i Γ x y e₁ e₂ r t _
      intro γ ρ hE
      obtain ⟨vx, hlkγx, htd_x, hcl_x, _, hbool_x⟩ := EnvAgrees.lookup_some hE hlk
      simp only [TyDenote] at htd_x
      obtain ⟨bx, hvxeq, _⟩ := htd_x
      subst hvxeq
      have hρx : ρ.bools x = bx := hbool_x bx rfl
      have hγcl := EnvAgrees.allClosed hE
      have hxfv := Exp.substEnv_var_lookup x γ (.bconst bx) hlkγx hcl_x hγcl
      simp only [Val.toExp] at hxfv
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
      cases bx with
      | true =>
        -- Extended EnvAgrees for e₁ branch: bind fresh `y`, keep `x : {ν|r}` intact.
        have hE₁ : EnvAgrees κ ((y, .refine .bool r_true) :: Γ)
            ((y, .bconst (ρ.bools y)) :: γ) ρ := by
          refine ⟨rfl, hE, ?_, fun n h => by simp at h, fun b h => ?_⟩
          · -- TyDenote for the guard: reduces to `ρ.bools x = true` (= hρx)
            simp only [TyDenote, r_true]
            refine ⟨ρ.bools y, rfl, ?_⟩
            simp [Refinement.interp, Formula.interp, Term.interp, REnv.get, hνx, hρx]
          · injection h
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_e₁ hE₁
        -- substEnv ((y,·)::γ) e₁ = substEnv γ e₁ since `y ∉ e₁.fv`
        rw [Exp.substEnv_cons_fresh e₁ γ y (.bconst (ρ.bools y)) hy_e₁] at hbs_vr
        refine ⟨vr, ?_, htd_vr⟩
        rw [Exp.substEnv_ite, hxfv]
        exact BigStep.ite_t BigStep.bconst hbs_vr
      | false =>
        -- Extended EnvAgrees for e₂ branch: bind fresh `y`, keep `x : {ν|r}` intact.
        have hE₂ : EnvAgrees κ ((y, .refine .bool r_false) :: Γ)
            ((y, .bconst (ρ.bools y)) :: γ) ρ := by
          refine ⟨rfl, hE, ?_, fun n h => by simp at h, fun b h => ?_⟩
          · simp only [TyDenote, r_false]
            refine ⟨ρ.bools y, rfl, ?_⟩
            simp [Refinement.interp, Formula.interp, Term.interp, REnv.get, hνx, hρx]
          · injection h
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_e₂ hE₂
        rw [Exp.substEnv_cons_fresh e₂ γ y (.bconst (ρ.bools y)) hy_e₂] at hbs_vr
        refine ⟨vr, ?_, htd_vr⟩
        rw [Exp.substEnv_ite, hxfv]
        exact BigStep.ite_f BigStep.bconst hbs_vr

/-! ## T3 — Closed-term type safety (corollary of T2) -/

theorem type_safety {κ : KEnv} {e : Exp} {t : Ty} (h : Hastype κ [] e t) :
    ∃ v, BigStep e v ∧ TyDenote κ t REnv.empty v := by
  obtain ⟨v, hbs, hv⟩ :=
    hastype_fundamental h (γ := []) (ρ := REnv.empty) (by simp [EnvAgrees])
  exact ⟨v, by simpa [Exp.substEnv] using hbs, hv⟩

/-! ## T4 — End-to-end VCGen safety

  The POPL headline: VCGen soundness composes with the logical-relations
  fundamental lemma to give end-to-end refinement type safety for `topVC`. -/

theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t) :
    ∃ v, BigStep e v ∧ TyDenote κ t REnv.empty v :=
  type_safety (topVC_decl_sound κ e t hE ht h)
