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
  apply REnv.ext
  · funext w
    by_cases hxw : x = w <;> by_cases hzw : z = w <;> simp_all
  · rfl

/-- Helper: writing a fresh `x` (`x ∉ r.fv`) does not change `Refinement.interp`.
    ν is pushed on the de Bruijn stack on both sides, so the fresh-name write
    commutes past it via `push_write_comm` and the refinement never reads `x`. -/
private theorem Refinement.interp_write_fresh {κ : KEnv} {b : Base} (r : Refinement b)
    (x : EVar) (va : Val) (γ : REnv)
    (hx : x ∉ Refinement.fv r)
    {w : b.interp} :
    Refinement.interp κ r γ w ↔ Refinement.interp κ r (γ.write x va) w := by
  cases r with
  | fmla φ =>
    simp only [Refinement.fv] at hx
    simp only [Refinement.interp]
    rw [REnv.push_write_comm]
    exact (Formula.interp_write_fresh φ x va (γ.push (Val.inj b w)) hx).symm
  | kapp kn args =>
    have hargs : ∀ a ∈ args, x ∉ Term.fv a.2 := fun a ha hm =>
      hx (by simp only [Refinement.fv, List.mem_flatMap]; exact ⟨a, ha, hm⟩)
    simp only [Refinement.interp]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    congr 1
    rw [REnv.push_write_comm]
    exact (Term.interp_write_fresh a.2 x va (γ.push (Val.inj b w)) (hargs a ha)).symm

/-- Combined Iff proved by strong induction on `t.skel`.
    Derives both `extendBy_fresh` and `of_extendBy_fresh` as corollaries. -/
private theorem TyDenote.extendBy_fresh_iff_aux (n : Nat) :
    ∀ (κ : KEnv) (t : Ty) (_ : t.skel ≤ n) (γ : REnv) (v : Val)
      (x : EVar) (va : Val)
      (_ : x ∉ t.fv),
      TyDenote κ t γ v ↔ TyDenote κ t (γ.write x va) v := by
  induction n with
  | zero =>
    intro κ t hn γ v x va hx
    match t with
    | .refine b r =>
      have hx' : x ∉ Refinement.fv r := by simpa [Ty.fv] using hx
      cases b <;> simp only [TyDenote] <;> constructor
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx').mp hp⟩
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx').mpr hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx').mp hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx').mpr hp⟩
    | .arrow _ _ => simp [Ty.skel] at hn
  | succ n ih =>
    intro κ t hn γ v x va hx
    match t with
    | .refine b r =>
      have hx' : x ∉ Refinement.fv r := by simpa [Ty.fv] using hx
      cases b <;> simp only [TyDenote] <;> constructor
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx').mp hp⟩
      · intro ⟨m, hvm, hp⟩; exact ⟨m, hvm, (Refinement.interp_write_fresh r x va γ hx').mpr hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx').mp hp⟩
      · intro ⟨b, hvb, hp⟩; exact ⟨b, hvb, (Refinement.interp_write_fresh r x va γ hx').mpr hp⟩
    | .arrow s' t' =>
      simp only [Ty.skel] at hn
      have hns' : s'.skel ≤ n := by omega
      have hnt' : t'.skel ≤ n := by omega
      simp only [Ty.fv, List.mem_append, not_or] at hx
      simp only [TyDenote]
      constructor
      · -- extendBy_fresh direction: γ → extendBy s γ x va
        intro ⟨body, hvclos, hlc, hcl, hLR⟩
        refine ⟨body, hvclos, hlc, hcl, fun va' htd_va' => ?_⟩
        have htd_va'_γ : TyDenote κ s' γ va' :=
          (ih κ s' hns' γ va' x va hx.1).mpr htd_va'
        obtain ⟨vr, hbs_vr, htd_vr⟩ := hLR va' htd_va'_γ
        -- htd_vr : TyDenote κ t' (γ.push va') vr; goal under (γ.write x va).push va'
        refine ⟨vr, hbs_vr, ?_⟩
        rw [REnv.push_write_comm]
        exact (ih κ t' hnt' (γ.push va') vr x va hx.2).mp htd_vr
      · -- of_extendBy_fresh direction: extendBy s γ x va → γ
        intro ⟨body, hvclos, hlc, hcl, hLR⟩
        refine ⟨body, hvclos, hlc, hcl, fun va' htd_va' => ?_⟩
        have htd_va'_ext : TyDenote κ s' (γ.write x va) va' :=
          (ih κ s' hns' γ va' x va hx.1).mp htd_va'
        obtain ⟨vr, hbs_vr, htd_vr⟩ := hLR va' htd_va'_ext
        -- htd_vr : TyDenote κ t' ((γ.write x va).push va') vr
        rw [REnv.push_write_comm] at htd_vr
        exact ⟨vr, hbs_vr, (ih κ t' hnt' (γ.push va') vr x va hx.2).mpr htd_vr⟩

/-- TyDenote is monotone under writing at a variable `x` not free in `t`. -/
theorem TyDenote.extendBy_fresh {κ : KEnv} {t : Ty} {γ : REnv} {v : Val}
    (x : EVar) (va : Val)
    (hx : x ∉ t.fv)
    (h : TyDenote κ t γ v) :
    TyDenote κ t (γ.write x va) v := by
  cases t with
  | refine b r =>
    have hx' : x ∉ Refinement.fv r := by simpa [Ty.fv] using hx
    cases b with
    | int =>
      simp only [TyDenote] at h ⊢
      obtain ⟨n, hvn, hp⟩ := h
      exact ⟨n, hvn, (Refinement.interp_write_fresh r x va γ hx').mp hp⟩
    | bool =>
      simp only [TyDenote] at h ⊢
      obtain ⟨bv, hvb, hp⟩ := h
      exact ⟨bv, hvb, (Refinement.interp_write_fresh r x va γ hx').mp hp⟩
  | arrow s' t' =>
    exact (TyDenote.extendBy_fresh_iff_aux (Ty.arrow s' t').skel κ (.arrow s' t') (by omega) γ v x va hx).mp h

/-- Reverse direction: TyDenote under a fresh write implies TyDenote at γ. -/
theorem TyDenote.of_extendBy_fresh {κ : KEnv} {t : Ty} {γ : REnv} {v : Val}
    (x : EVar) (va : Val)
    (hx : x ∉ t.fv)
    (h : TyDenote κ t (γ.write x va) v) :
    TyDenote κ t γ v :=
  (TyDenote.extendBy_fresh_iff_aux t.skel κ t (by omega) γ v x va hx).mpr h

/-! ## push ↔ openVar bridge

  The new `TyDenote` threads arrow-binder values through the de Bruijn stack
  (`γ.push va`), like `Formula.interp` does for quantifiers. Relating that to the
  *non-shifting* `openVar` needs a de Bruijn substitution lemma: inserting a value
  at stack index `m` (`insertBV`) equals opening `BVar m` to a fresh name `x` whose
  value is written into the name map, provided no `BVar` sits above level `m` (so
  the shifted region of the stack is empty). The old intermediate `substBV` is
  fused away: each `interp_insertBV_openBVar` lemma proves the bridge directly. -/

private theorem getElem?_insertIdx_lt {α} (l : List α) (m j : Nat) (a : α)
    (h : j < m) : (l.insertIdx m a)[j]? = l[j]? := by
  induction l generalizing m j with
  | nil => cases m with
    | zero => omega
    | succ m => simp [List.insertIdx]
  | cons b l ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [List.insertIdx]
      cases j with
      | zero => rfl
      | succ j => simp only [List.getElem?_cons_succ]; exact ih m j (by omega)

/-- Reading a `Term` after inserting `Val.inj b v` at stack level `m` equals
    reading the `openBVar`-opened term under `x ↦ v` in the name map, given `x`
    fresh and no `BVar` above level `m` (base `b` at `m`). This fuses the old
    insertBV↔substBV and substBV↔openBVar steps into one direct induction. -/
private theorem Term.interp_insertBV_openBVar {b'' : Base} (t : Term b'') (b : Base) (m : Nat)
    (v : b.interp) (x : EVar) (γ : REnv) (hlen : m ≤ γ.bv.length) (hx : x ∉ t.fv)
    (hwf : ∀ (b' : Base) (j : Nat), Term.hasBVar b' j t → j < m ∨ (j = m ∧ b' = b)) :
    Term.interp (γ.insertBV m (Val.inj b v)) t =
    Term.interp (γ.update b x v) (t.openBVar b m x) := by
  induction t with
  | const _ _ => rfl
  | bvar b' j =>
    have hwfj : j < m ∨ (j = m ∧ b' = b) := hwf b' j (by simp [Term.hasBVar])
    simp only [Term.interp, REnv.getBV, REnv.insertBV_bv]
    rcases hwfj with hjm | ⟨hjeq, hbeq⟩
    · -- j < m: open doesn't fire (j ≠ m), insert doesn't shift, update keeps bv
      rw [getElem?_insertIdx_lt γ.bv m j (Val.inj b v) hjm]
      cases b <;> cases b' <;>
        simp [Term.openBVar, Term.interp, REnv.getBV, Nat.ne_of_lt hjm]
    · -- j = m, b' = b: insert puts `inj b v` here; open turns it into `fvar b x`
      subst hjeq
      rw [List.getElem?_insertIdx_self, if_pos hlen]
      cases b <;> cases b' <;>
        simp_all [Term.openBVar, Term.interp, REnv.get]
  | fvar b' z =>
    have hxz : x ≠ z := fun h => hx (by subst h; simp [Term.fv])
    simp only [Term.openBVar, Term.interp]
    cases b' <;> cases b <;> simp_all [REnv.get]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at hx
    simp only [Term.interp, Term.openBVar,
      ih₁ hx.1 (fun b' j h => hwf b' j (by simp [Term.hasBVar, h])),
      ih₂ hx.2 (fun b' j h => hwf b' j (by simp [Term.hasBVar, h]))]
  | not t ih =>
    simp only [Term.fv] at hx
    simp only [Term.interp, Term.openBVar,
      ih hx (fun b' j h => hwf b' j (by simp [Term.hasBVar, h]))]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at hx
    simp only [Term.interp, Term.openBVar,
      ih₁ hx.1 (fun b' j h => hwf b' j (by simp [Term.hasBVar, h])),
      ih₂ hx.2 (fun b' j h => hwf b' j (by simp [Term.hasBVar, h]))]

/-- `Term` version with no `BVar` at level `≥ m`: inserting any `w` is invisible. -/
private theorem Term.interp_insertBV_fresh {b'' : Base} (t : Term b'') (m : Nat)
    (w : Val) (γ : REnv)
    (hwf : ∀ (b' : Base) (j : Nat), Term.hasBVar b' j t → j < m) :
    Term.interp (γ.insertBV m w) t = Term.interp γ t := by
  induction t with
  | const _ _ => rfl
  | bvar b' j =>
    have : j < m := hwf b' j (by simp [Term.hasBVar])
    simp only [Term.interp, REnv.getBV, REnv.insertBV_bv,
               getElem?_insertIdx_lt γ.bv m j w this]
  | fvar _ _ => rfl
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.interp, ih₁ (fun b' j h => hwf b' j (by simp [Term.hasBVar, h])),
               ih₂ (fun b' j h => hwf b' j (by simp [Term.hasBVar, h]))]
  | not t ih => simp only [Term.interp, ih (fun b' j h => hwf b' j (by simp [Term.hasBVar, h]))]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.interp, ih₁ (fun b' j h => hwf b' j (by simp [Term.hasBVar, h])),
               ih₂ (fun b' j h => hwf b' j (by simp [Term.hasBVar, h]))]

/-- `Formula` version of `Term.interp_insertBV_openBVar`. Quantifiers bump the
    level (both the inserted index and the opened level). -/
private theorem Formula.interp_insertBV_openBVar (φ : Formula) (b : Base) (m : Nat)
    (v : b.interp) (x : EVar) (γ : REnv) (hlen : m ≤ γ.bv.length) (hx : x ∉ φ.fv)
    (hwf : ∀ (b' : Base) (j : Nat), Formula.hasBVar b' j φ → j < m ∨ (j = m ∧ b' = b)) :
    Formula.interp (γ.insertBV m (Val.inj b v)) φ ↔
    Formula.interp (γ.update b x v) (φ.openBVar b m x) := by
  induction φ generalizing m γ with
  | tt | ff => rfl
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hx
    simp only [Formula.interp, Formula.openBVar,
      Term.interp_insertBV_openBVar t₁ b m v x γ hlen hx.1
        (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h])),
      Term.interp_insertBV_openBVar t₂ b m v x γ hlen hx.2
        (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h]))]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hx
    simp only [Formula.interp, Formula.openBVar,
      ih₁ m γ hlen hx.1 (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h])),
      ih₂ m γ hlen hx.2 (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h]))]
  | not φ ih =>
    simp only [Formula.fv] at hx
    simp only [Formula.interp, Formula.openBVar,
      ih m γ hlen hx (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h]))]
  | ex b' φ ih | all b'' φ ih =>
    simp only [Formula.fv] at hx
    simp only [Formula.interp, Formula.openBVar]
    have hwf' : ∀ (b'' : Base) (j : Nat),
        Formula.hasBVar b'' j φ → j < m + 1 ∨ (j = m + 1 ∧ b'' = b) := by
      intro b' j h
      rcases j with _ | j
      · exact Or.inl (by omega)
      · rcases hwf b' j (by simpa [Formula.hasBVar] using h) with h' | ⟨h', hb⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, hb⟩
    first
    | exact exists_congr (fun n => by
        rw [REnv.push_insertBV_comm, REnv.push_update_comm]
        exact ih (m+1) (γ.push (Val.inj b' n)) (Nat.succ_le_succ hlen) hx hwf')
    | exact forall_congr' (fun n => by
        rw [REnv.push_insertBV_comm, REnv.push_update_comm]
        exact ih (m+1) (γ.push (Val.inj b'' n)) (Nat.succ_le_succ hlen) hx hwf')

/-- `Formula` version with no `BVar` at level `≥ m`: inserting any `w` is invisible. -/
private theorem Formula.interp_insertBV_fresh (φ : Formula) (m : Nat) (w : Val) (γ : REnv)
    (hwf : ∀ (b' : Base) (j : Nat), Formula.hasBVar b' j φ → j < m) :
    Formula.interp (γ.insertBV m w) φ ↔ Formula.interp γ φ := by
  induction φ generalizing m γ with
  | tt | ff => rfl
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.interp,
      Term.interp_insertBV_fresh t₁ m w γ (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h])),
      Term.interp_insertBV_fresh t₂ m w γ (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h]))]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.interp,
      ih₁ m γ (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h])),
      ih₂ m γ (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h]))]
  | not φ ih =>
    simp only [Formula.interp, ih m γ (fun b' j h => hwf b' j (by simp [Formula.hasBVar, h]))]
  | ex b φ ih | all b φ ih =>
    simp only [Formula.interp]
    have hwf' : ∀ (b' : Base) (j : Nat), Formula.hasBVar b' j φ → j < m + 1 := by
      intro b' j h; rcases j with _ | j
      · omega
      · have := hwf b' j (by simpa [Formula.hasBVar] using h); omega
    first
    | exact exists_congr (fun n => by rw [REnv.push_insertBV_comm]; exact ih (m+1) (γ.push (Val.inj b n)) hwf')
    | exact forall_congr' (fun n => by rw [REnv.push_insertBV_comm]; exact ih (m+1) (γ.push (Val.inj b n)) hwf')

/-- `Refinement` version of `Formula.interp_insertBV_openBVar` (ν is pushed first,
    so the inserted/opened level shifts to `m+1`). -/
private theorem Refinement.interp_insertBV_openBVar {b' : Base} (κ : KEnv) (r : Refinement b')
    (b : Base) (m : Nat) (v : b.interp) (x : EVar) (γ : REnv) (ν : b'.interp)
    (hlen : m ≤ γ.bv.length) (hx : x ∉ Refinement.fv r)
    (hwf : ∀ (b'' : Base) (j : Nat), Refinement.hasBVar b'' j r → j < m+1 ∨ (j = m+1 ∧ b'' = b)) :
    Refinement.interp κ r (γ.insertBV m (Val.inj b v)) ν ↔
    Refinement.interp κ (r.openBVar b (m+1) x) (γ.update b x v) ν := by
  cases r with
  | fmla φ =>
    simp only [Refinement.fv] at hx
    simp only [Refinement.interp, Refinement.openBVar,
      REnv.push_insertBV_comm, REnv.push_update_comm]
    exact Formula.interp_insertBV_openBVar φ b (m+1) v x (γ.push (Val.inj b' ν))
      (Nat.succ_le_succ hlen) hx
      (fun b'' j h => hwf b'' j (by simpa [Refinement.hasBVar] using h))
  | kapp kn args =>
    simp only [Refinement.interp, Refinement.openBVar,
      REnv.push_insertBV_comm, REnv.push_update_comm]
    apply Iff.of_eq; congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    have hxa : x ∉ Term.fv a.2 := fun hm =>
      hx (by simp only [Refinement.fv, List.mem_flatMap]; exact ⟨a, ha, hm⟩)
    simp only [Function.comp]; congr 1
    exact Term.interp_insertBV_openBVar a.2 b (m+1) v x (γ.push (Val.inj b' ν))
      (Nat.succ_le_succ hlen) hxa
      (fun b'' j h => hwf b'' j (by simp only [Refinement.hasBVar]; exact ⟨a, ha, h⟩))

/-- `Refinement` version with no `BVar` at level `≥ m+1`: inserting `w` is invisible. -/
private theorem Refinement.interp_insertBV_fresh {b' : Base} (κ : KEnv) (r : Refinement b')
    (m : Nat) (w : Val) (γ : REnv) (ν : b'.interp)
    (hwf : ∀ (b'' : Base) (j : Nat), Refinement.hasBVar b'' j r → j < m+1) :
    Refinement.interp κ r (γ.insertBV m w) ν ↔ Refinement.interp κ r γ ν := by
  cases r with
  | fmla φ =>
    simp only [Refinement.interp, REnv.push_insertBV_comm]
    exact Formula.interp_insertBV_fresh φ (m+1) w (γ.push (Val.inj b' ν))
      (fun b'' j h => hwf b'' j (by simpa [Refinement.hasBVar] using h))
  | kapp kn args =>
    simp only [Refinement.interp, REnv.push_insertBV_comm]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    congr 1
    exact Term.interp_insertBV_fresh a.2 (m+1) w (γ.push (Val.inj b' ν))
      (fun b'' j h => hwf b'' j (by simp only [Refinement.hasBVar]; exact ⟨a, ha, h⟩))

/-- Index helper: a `BVar` at level `j` in `some b :: (ρ ++ [some bb])` is either
    below `ρ.length+1`, or exactly at `ρ.length+1` with base `bb`. -/
private theorem wfbv_index_split (b bb b'' : Base) (ρ : List (Option Base)) (j : Nat)
    (h : (some b :: (ρ ++ [some bb]))[j]? = some (some b'')) :
    j < ρ.length + 1 ∨ (j = ρ.length + 1 ∧ b'' = bb) := by
  rcases j with _ | j
  · exact Or.inl (by omega)
  · simp only [List.getElem?_cons_succ, List.getElem?_append] at h
    by_cases hj : j < ρ.length
    · simp only [hj] at h; left; omega
    · have : ρ.length ≤ j := by omega
      simp only [Nat.not_lt.mpr this] at h
      by_cases hje : j = ρ.length
      · subst hje; simp at h; right; exact ⟨by omega, h.symm⟩
      · exfalso; have : j - ρ.length ≠ 0 := by omega
        rcases hh : j - ρ.length with _ | k
        · omega
        · simp [hh] at h

/-- Index helper for the `none` slot: a `BVar` at level `j` in
    `some b :: (ρ ++ [none])` must be below `ρ.length+1`. -/
private theorem wfbv_index_none (b b'' : Base) (ρ : List (Option Base)) (j : Nat)
    (h : (some b :: (ρ ++ [none]))[j]? = some (some b'')) :
    j < ρ.length + 1 := by
  rcases j with _ | j
  · omega
  · simp only [List.getElem?_cons_succ, List.getElem?_append] at h
    by_cases hj : j < ρ.length
    · omega
    · have : ρ.length ≤ j := by omega
      simp only [Nat.not_lt.mpr this] at h
      rcases hh : j - ρ.length with _ | k <;> simp [hh] at h

/-- A denoting value carries the base of its type. -/
private theorem Val.optBase_of_tyDenote {κ : KEnv} {s : Ty} {γ : REnv} {va : Val}
    (h : TyDenote κ s γ va) : Val.optBase va = s.optBase := by
  cases s with
  | refine b r => cases b <;> (simp only [TyDenote] at h; obtain ⟨w, rfl, _⟩ := h; rfl)
  | arrow _ _ => simp only [TyDenote] at h; obtain ⟨body, rfl, _⟩ := h; rfl

/-- Master bridge (push ↔ openVar): interpreting `t` with `va` inserted at de
    Bruijn level `ρ.length` equals interpreting `t.openVar` with `x ↦ va` written
    into the name map. The `ρ` context lists the (live) enclosing binder bases;
    `[Val.optBase va]` is the inserted binder's base. The arrow case is clean
    (`push_write_comm`); the leaf is the fused `interp_insertBV_openBVar`
    (insertBV↔openBVar directly, no `substBV` intermediate). -/
private theorem TyDenote.insertBV_openVar_aux (n : Nat) :
    ∀ (ρ : List (Option Base)) (κ : KEnv) (t : Ty) (_ : t.skel ≤ n)
      (x : EVar) (γ : REnv) (va : Val) (v : Val)
      (_ : Ty.WFBVarCtx (ρ ++ [Val.optBase va]) t)
      (_ : ρ.length ≤ γ.bv.length)
      (_ : x ∉ t.fv),
      TyDenote κ t (γ.insertBV ρ.length va) v ↔
      TyDenote κ (t.openVar ρ.length x) (γ.write x va) v := by
  induction n with
  | zero =>
    intro ρ κ t hsk x γ va v hwfb hlen hxf
    cases t <;> simp at hsk
    rename_i b r
    simp only [Ty.WFBVarCtx] at hwfb
    simp only [Ty.fv] at hxf
    have hx_rfv : x ∉ Refinement.fv r := hxf
    cases va with
    | iconst m =>
      simp only [Val.optBase] at hwfb
      simp only [Ty.openVar]
      rw [Refinement.openBVar_noop (r.openBVar .int (ρ.length+1) x) .bool (ρ.length+1) x (by
            intro hbv
            rw [Refinement.hasBVar_openBVar_other r .bool .int (ρ.length+1) (ρ.length+1) x
                  (Or.inl (by decide))] at hbv
            rcases wfbv_index_split b .int .bool ρ (ρ.length+1) (hwfb .bool (ρ.length+1) hbv) with h | ⟨_, h⟩
            · omega
            · exact absurd h (by decide))]
      have hwf : ∀ (b'' : Base) (j : Nat), Refinement.hasBVar b'' j r →
          j < ρ.length + 1 ∨ (j = ρ.length + 1 ∧ b'' = .int) :=
        fun b'' j h => wfbv_index_split b .int b'' ρ j (hwfb b'' j h)
      cases b <;> simp only [TyDenote] <;>
        exact exists_congr (fun w => and_congr_right (fun _ =>
          Refinement.interp_insertBV_openBVar κ r .int ρ.length m x γ w hlen hx_rfv hwf))
    | bconst c =>
      simp only [Val.optBase] at hwfb
      simp only [Ty.openVar]
      rw [Refinement.openBVar_noop r .int (ρ.length+1) x (by
            intro hbv
            rcases wfbv_index_split b .bool .int ρ (ρ.length+1) (hwfb .int (ρ.length+1) hbv) with h | ⟨_, h⟩
            · omega
            · exact absurd h (by decide))]
      have hwf : ∀ (b'' : Base) (j : Nat), Refinement.hasBVar b'' j r →
          j < ρ.length + 1 ∨ (j = ρ.length + 1 ∧ b'' = .bool) :=
        fun b'' j h => wfbv_index_split b .bool b'' ρ j (hwfb b'' j h)
      cases b <;> simp only [TyDenote] <;>
        exact exists_congr (fun w => and_congr_right (fun _ =>
          Refinement.interp_insertBV_openBVar κ r .bool ρ.length c x γ w hlen hx_rfv hwf))
    | clos body =>
      simp only [Val.optBase] at hwfb
      simp only [Ty.openVar]
      have hwf : ∀ (b'' : Base) (j : Nat), Refinement.hasBVar b'' j r → j < ρ.length + 1 :=
        fun b'' j h => wfbv_index_none b b'' ρ j (hwfb b'' j h)
      rw [Refinement.openBVar_noop r .int (ρ.length+1) x
            (fun hbv => absurd (hwf .int (ρ.length+1) hbv) (by omega)),
          Refinement.openBVar_noop r .bool (ρ.length+1) x
            (fun hbv => absurd (hwf .bool (ρ.length+1) hbv) (by omega))]
      cases b <;> simp only [TyDenote] <;>
        exact exists_congr (fun w => and_congr_right (fun _ =>
          (Refinement.interp_insertBV_fresh κ r ρ.length (.clos body) γ w hwf).trans
          (Refinement.interp_write_fresh r x (.clos body) γ hx_rfv)))
  | succ n ih =>
    intro ρ κ t hsk x γ va v hwfb hlen hxf
    by_cases hn : t.skel ≤ n
    · exact ih ρ κ t hn x γ va v hwfb hlen hxf
    · match t with
      | .refine b r => simp [Ty.skel] at hn
      | .arrow s' t' =>
        simp only [Ty.skel] at hsk hn
        simp only [Ty.fv, List.mem_append, not_or] at hxf
        obtain ⟨hwfb_s', hwfb_t'⟩ : Ty.WFBVarCtx (ρ ++ [Val.optBase va]) s' ∧
            Ty.WFBVarCtx (s'.optBase :: ρ ++ [Val.optBase va]) t' := hwfb
        simp only [Ty.openVar, TyDenote]
        refine exists_congr (fun body => and_congr_right (fun _ => and_congr_right (fun _ =>
          and_congr_right (fun _ => ?_))))
        constructor
        · -- insertBV-form → openVar-form
          intro hLR va' htd_va'
          have htd_va'_ins : TyDenote κ s' (γ.insertBV ρ.length va) va' :=
            (ih ρ κ s' (by omega) x γ va va' hwfb_s' hlen hxf.1).mpr htd_va'
          obtain ⟨vr, hbs, htd_vr⟩ := hLR va' htd_va'_ins
          rw [REnv.push_insertBV_comm] at htd_vr
          refine ⟨vr, hbs, ?_⟩
          rw [REnv.push_write_comm]
          exact (ih (s'.optBase :: ρ) κ t' (by omega) x (γ.push va') va vr
            (by simpa using hwfb_t') (Nat.succ_le_succ hlen) hxf.2).mp htd_vr
        · -- openVar-form → insertBV-form
          intro hLR va' htd_va'
          have htd_va'_ov : TyDenote κ (s'.openVar ρ.length x) (γ.write x va) va' :=
            (ih ρ κ s' (by omega) x γ va va' hwfb_s' hlen hxf.1).mp htd_va'
          obtain ⟨vr, hbs, htd_vr⟩ := hLR va' htd_va'_ov
          rw [REnv.push_write_comm] at htd_vr
          refine ⟨vr, hbs, ?_⟩
          rw [REnv.push_insertBV_comm]
          exact (ih (s'.optBase :: ρ) κ t' (by omega) x (γ.push va') va vr
            (by simpa using hwfb_t') (Nat.succ_le_succ hlen) hxf.2).mpr htd_vr

/-- `push va` in TyDenote corresponds to `openVar 0 x` with `γ.write x va`,
    when x is fresh for t, va is compatible with s (TyDenote κ s γ va), and t is
    well-formed (WFBVarCtx [s.optBase] t) so that only the correct-base BVars appear. -/
theorem TyDenote.push_iff (κ : KEnv) (t : Ty) (s : Ty) (x : EVar) (γ : REnv)
    (va : Val) (v : Val)
    (hx_fv : x ∉ t.fv)
    (hWF : Ty.WFBVarCtx [s.optBase] t)
    (hcompat : TyDenote κ s γ va) :
    TyDenote κ t (γ.push va) v ↔
    TyDenote κ (t.openVar 0 x) (γ.write x va) v := by
  -- `va` carries `s`'s base, so `WFBVarCtx [s.optBase] t = WFBVarCtx [Val.optBase va] t`.
  have hvb : Val.optBase va = s.optBase := Val.optBase_of_tyDenote hcompat
  have h := TyDenote.insertBV_openVar_aux t.skel [] κ t (Nat.le_refl _) x γ va v
    (by simp only [List.nil_append, hvb]; exact hWF) (by simp) hx_fv
  simpa using h

/-- `EnvCloses` is preserved when extending `γ` at a name `x` fresh for Γ
    (the existing bindings never read `x`). -/
theorem EnvCloses.extendBy_fresh {κ Γ γ} (hE : EnvCloses κ Γ γ)
    (x : EVar) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) :
    EnvCloses κ Γ (γ.write x va) := by
  induction Γ with
  | nil => exact True.intro
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    obtain ⟨htd, hΓ⟩ := hE
    simp only [TEnv.dom, List.mem_cons, not_or] at hx_dom
    simp only [TEnv.tyFv, List.mem_append, not_or] at hx_fv
    have hxy : x ≠ y := hx_dom.1
    refine ⟨?_, ih hΓ hx_dom.2 hx_fv.2⟩
    rw [REnv.write_other γ x va hxy]
    exact TyDenote.extendBy_fresh x va hx_fv.1 htd

/-- Extend `EnvCloses` by prepending a fresh `(x, s)` binding whose value `va`
    is the value written at `x`. The single-env analogue of `EnvAgrees.extend`;
    the reflection clauses are gone since the slot value is `va` by `write_self`. -/
theorem EnvCloses.extend {κ Γ γ} (hE : EnvCloses κ Γ γ)
    (x : EVar) (s : Ty) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ)
    (htd : TyDenote κ s (γ.write x va) va) :
    EnvCloses κ ((x, s) :: Γ) (γ.write x va) := by
  refine ⟨?_, EnvCloses.extendBy_fresh hE x va hx_dom hx_fv⟩
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
    (hz_fv : z ∉ TEnv.tyFv Γ) :
    ModelsEnv κ (γ.write z va) Γ := by
  induction Γ with
  | nil => exact True.intro
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    simp only [TEnv.dom, List.mem_cons, not_or] at hz_dom
    simp only [TEnv.tyFv, List.mem_append, not_or] at hz_fv
    cases t with
    | arrow s' t' =>
      simp only [ModelsEnv] at hm ⊢
      exact ih hm hz_dom.2 hz_fv.2
    | refine b r =>
      simp only [ModelsEnv] at hm ⊢
      obtain ⟨hHB, hhead, htail⟩ := hm
      have hzy : z ≠ y := hz_dom.1
      have hmap : (γ.write z va).map y = γ.map y :=
        REnv.write_other γ z va hzy
      refine ⟨?_, ?_, ih htail hz_dom.2 hz_fv.2⟩
      · cases b with
        | int  => obtain ⟨n, hn⟩ := hHB; exact ⟨n, by rw [hmap]; exact hn⟩
        | bool => obtain ⟨c, hc⟩ := hHB; exact ⟨c, by rw [hmap]; exact hc⟩
      · have hz_rfv : z ∉ Refinement.fv r := by simpa [Ty.fv] using hz_fv.1
        have hget : REnv.get b (γ.write z va) y = REnv.get b γ y := by simp_all only [REnv.get, REnv.lookup]
        rw [hget]
        exact (Refinement.interp_write_fresh r z va γ hz_rfv).mp hhead

/-- Build ModelsEnv after prepending a fresh binding (z, s₂). -/
private theorem ModelsEnv.extendBy_cons {κ : KEnv} {Γ : TEnv} {γ : REnv}
    (hm : ModelsEnv κ γ Γ) (s₂ : Ty) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_s2fv : z ∉ s₂.fv)
    (htd_va : TyDenote κ s₂ γ va) :
    ModelsEnv κ (γ.write z va) ((z, s₂) :: Γ) := by
  have htail := ModelsEnv.extendBy_fresh_aux hm z va hz_dom hz_fv
  cases s₂ with
  | arrow s' t' => simp only [ModelsEnv]; exact htail
  | refine b r =>
    simp only [ModelsEnv]
    have hz_rfv : z ∉ Refinement.fv r := by simpa [Ty.fv] using hz_s2fv
    cases b with
    | int =>
      simp only [TyDenote] at htd_va
      obtain ⟨n, hvn, hp⟩ := htd_va; subst hvn
      refine ⟨⟨n, ?_⟩, ?_, htail⟩
      · simp
      · simp only [REnv.get_update_same]
        exact (Refinement.interp_write_fresh r z (.iconst n) γ hz_rfv).mp hp
    | bool =>
      simp only [TyDenote] at htd_va
      obtain ⟨bv, hvb, hp⟩ := htd_va; subst hvb
      refine ⟨⟨bv, ?_⟩, ?_, htail⟩
      · simp
      · simp only [REnv.get_update_same]
        exact (Refinement.interp_write_fresh r z (.bconst bv) γ hz_rfv).mp hp

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
    simp only [List.mem_append, not_or] at hfresh
    obtain ⟨⟨⟨⟨⟨hx_Γdom, hx_Γfv⟩, hx_s1fv⟩, hx_s2fv⟩, hx_t1fv⟩, hx_t2fv⟩ := hfresh
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
    -- Convert (t₁ under γ.push va) ↔ t₁.openVar 0 x under γ.write x va
    rw [TyDenote.push_iff κ t₁ s₂ x γ va vr hx_t1fv hWF_st1' htd_va]
      at htd_vr_t1
    -- Build extended model for ((x, s₂) :: Γ')
    have hm_ext : ModelsEnv κ (γ.write x va) ((x, s₂) :: Γ') :=
      ModelsEnv.extendBy_cons hm s₂ x va hx_Γdom hx_Γfv hx_s2fv htd_va
    -- Apply codomain IH at x
    have htd_vr_t2 : TyDenote κ (t₂.openVar 0 x) (γ.write x va) vr :=
      ih_hcodom hWF_t1x hWF_t2x hm_ext htd_vr_t1
    -- Convert back: t₂.openVar 0 x ↔ t₂ under γ.push va
    exact (TyDenote.push_iff κ t₂ s₂ x γ va vr hx_t2fv hWF_t2 htd_va).mpr
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
  | add_var hlk₁ hlk₂ =>
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
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx, hγy]
  | leq_var hlk₁ hlk₂ =>
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
        simp only [Refinement.interp, Formula.interp, Term.interp,
                   REnv.getBV, REnv.get, REnv.lookup, REnv.push, Val.proj, Val.inj,
                   hγx, hγy, List.getElem?_cons_zero, Option.getD_some]
        constructor
        · intro h; exact decide_eq_true_iff.mp h
        · intro h; exact decide_eq_true_iff.mpr h
  | not_var hlk =>
      rename_i x r
      intro γ hE
      have hv₁ := EnvCloses.lookup hE hlk
      simp only [TyDenote] at hv₁; obtain ⟨b, hγx, _⟩ := hv₁
      have hx : Exp.substEnv γ (.fvar x) = .bconst b := by simp [Exp.substEnv_fvar, hγx]
      refine ⟨.bconst (!b), ?_, ?_⟩
      · rw [Exp.substEnv_not, hx]; exact BigStep.not_ BigStep.bconst
      · simp only [TyDenote]; refine ⟨!b, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx]
  | and_var hlkx hlky =>
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
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx, hγy]
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
      · -- LR: for any va : s₁, produce vr evaluating body and in s₂ under γ.push va
        intro va htd_va
        -- x is the witness from the constructor; extract freshness facts
        simp [List.mem_append, not_or] at hfresh
        obtain ⟨hxΓ, hxΓfv, hxbody, hxs₁, hxs₂⟩ := hfresh
        have htd_va_x : TyDenote κ s₁ (γ.write x va) va :=
          TyDenote.extendBy_fresh x va hxs₁ htd_va
        have hEx : EnvCloses κ ((x, s₁) :: Γ') (γ.write x va) :=
          EnvCloses.extend hE x s₁ va hxΓ hxΓfv htd_va_x
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_fund hEx
        rw [Exp.substEnv_write_openVar body γ va x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (hbody_dom w hw))] at hbs_vr
        have hWF_s₂ : Ty.WFBVarCtx [s₁.optBase] s₂ := hwf_arr.2
        exact ⟨vr, hbs_vr,
          (TyDenote.push_iff κ s₂ s₁ x γ va vr hxs₂ hWF_s₂ htd_va).mpr htd_vr⟩
  | app h_fn h_arg hyfv ih_fn ih_arg =>
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
        exact (TyDenote.push_iff κ t s y γ va vr hyfv hWF_t htd_arg).mp htd_vr
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
      obtain ⟨hxΓ, hxΓfv, hxbody, hxs, hxt⟩ := xf
      have htd₁_x : TyDenote κ s' (γ.write x v₁) v₁ :=
        TyDenote.extendBy_fresh x v₁ hxs htd₁
      have hEx : EnvCloses κ ((x, s') :: Γ') (γ.write x v₁) :=
        EnvCloses.extend hE x s' v₁ hxΓ hxΓfv htd₁_x
      obtain ⟨vr, hbs₂, htd_vr⟩ := ih₂ hEx
      rw [Exp.substEnv_write_openVar e₂ γ v₁ x 0 hxbody
            (fun w hw => EnvCloses.mem_lc hE (he₂_dom w hw))] at hbs₂
      have htd_vr_γ : TyDenote κ t' γ vr :=
        TyDenote.of_extendBy_fresh x v₁ hxt htd_vr
      rw [Exp.substEnv_letin]
      exact ⟨vr, BigStep.letin hbs₁ hbs₂, htd_vr_γ⟩
  | ite hlk hfresh _ h₁ h₂ ih_e₁ ih_e₂ =>
      rename_i Γ x y e₁ e₂ r t _
      intro γ hE
      have htd_x := EnvCloses.lookup hE hlk
      simp only [TyDenote] at htd_x
      obtain ⟨bx, hγx, _⟩ := htd_x
      have hxfv : Exp.substEnv γ (.fvar x) = .bconst bx := by simp [Exp.substEnv_fvar, hγx]
      -- `y` (the fresh guard) is not free in either branch.
      have hy_e₁ : y ∉ e₁.fv := fun hm => hfresh (by simp [hm])
      have hy_e₂ : y ∉ e₂.fv := fun hm => hfresh (by simp [hm])
      -- Fresh-guard refinements read `x` free (not ν); `y`'s own value is irrelevant.
      let r_true : Refinement .bool :=
        .fmla (.eq .bool (.fvar .bool x) (.const .bool true))
      let r_false : Refinement .bool :=
        .fmla (.eq .bool (.fvar .bool x) (.const .bool false))
      -- Freshness facts for `y` (all from `hfresh`).
      have hy_dom : y ∉ TEnv.dom Γ := fun hm => hfresh (by simp [hm])
      have hy_tyfv : y ∉ TEnv.tyFv Γ := fun hm => hfresh (by simp [hm])
      have hy_tfv : y ∉ t.fv := fun hm => hfresh (by simp [hm])
      have hyx : y ≠ x := fun he => hfresh (by simp [he])
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
                REnv.get, REnv.lookup, hyx, hγx]
        have hE₁ : EnvCloses κ ((y, .refine .bool r_true) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_true) (.bconst (γ.bools y))
            hy_dom hy_tyfv htd_guard
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_e₁ hE₁
        rw [Exp.substEnv_write_fresh e₁ γ y (.bconst (γ.bools y)) hy_e₁] at hbs_vr
        refine ⟨vr, ?_,
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv htd_vr⟩
        rw [Exp.substEnv_ite, hxfv]
        exact BigStep.ite_t BigStep.bconst hbs_vr
      | false =>
        have htd_guard : TyDenote κ (.refine .bool r_false)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, r_false]
          refine ⟨γ.bools y, rfl, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup, hyx, hγx]
        have hE₂ : EnvCloses κ ((y, .refine .bool r_false) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_false) (.bconst (γ.bools y))
            hy_dom hy_tyfv htd_guard
        obtain ⟨vr, hbs_vr, htd_vr⟩ := ih_e₂ hE₂
        rw [Exp.substEnv_write_fresh e₂ γ y (.bconst (γ.bools y)) hy_e₂] at hbs_vr
        refine ⟨vr, ?_,
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv htd_vr⟩
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
