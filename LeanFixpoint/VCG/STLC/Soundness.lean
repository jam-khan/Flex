import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness (skeleton, κ-indexed)

  Algorithmic VC generation is sound w.r.t. the bidirectional and declarative
  typing rules. Every judgement is now parameterized by `κ : KEnv`.

-/

/-! ## Sub soundness -/

theorem ty_open_replace {x y : EVar} {t₁ : Ty}
    (hxfv : x ∉ t₁.fv) (hxn : x ∉ Ty.named t₁) (hxν : x ≠ nuName) :
    Ty.openVar 0 x t₁ = Ty.refine b r₁ →
    Ty.openVar 0 y t₁ = Ty.refine b (r₁.replaceFVar x y) := by
  intro ht1
  have hopen : (Ty.openVar 0 x t₁).replaceFVar x y = Ty.openVar 0 y t₁ :=
    Ty.openVar_replace 0 x y t₁ hxfv hxn hxν
  rw [ht1] at hopen
  simp [Ty.replaceFVar] at hopen
  exact hopen.symm

/-- Refinements whose formula is fresh in `x` and `ν` are invariant under
    updating `ρ` at `.int x` (and likewise at `.bool x`). Wrapper around
    `Formula.interp_update_fresh_*`. -/
private theorem Refinement.interp_invariant_under_int_update
    {κ : KEnv} {b : Base} (r : Refinement b)
    (x : EVar) (vi : Int) (ρ : REnv) (v : b.interp)
    (hxfv : x ∉ r.fmla.fv) (hxn : x ∉ r.fmla.named) (hxν : x ≠ nuName) :
    Refinement.interp κ r (ρ.update .int x vi) v ↔ Refinement.interp κ r ρ v := by
  simp only [Refinement.interp]
  have hcomm : (ρ.update .int x vi).update b nuName v
             = (ρ.update b nuName v).update .int x vi := by
    cases b with
    | int  => exact (REnv.update_comm_int_int ρ nuName x v vi hxν.symm).symm
    | bool => exact (REnv.update_comm_int_bool ρ x nuName vi v).symm
  rw [hcomm]
  exact (Formula.interp_update_fresh_int κ r.fmla x vi
          (ρ.update b nuName v) hxfv hxn).symm

private theorem Refinement.interp_invariant_under_bool_update
    {κ : KEnv} {b : Base} (r : Refinement b)
    (x : EVar) (vb : Bool) (ρ : REnv) (v : b.interp)
    (hxfv : x ∉ r.fmla.fv) (hxn : x ∉ r.fmla.named) (hxν : x ≠ nuName) :
    Refinement.interp κ r (ρ.update .bool x vb) v ↔ Refinement.interp κ r ρ v := by
  simp only [Refinement.interp]
  have hcomm : (ρ.update .bool x vb).update b nuName v
             = (ρ.update b nuName v).update .bool x vb := by
    cases b with
    | int  => exact REnv.update_comm_int_bool ρ nuName x v vb
    | bool => exact (REnv.update_comm_bool_bool ρ nuName x v vb hxν.symm).symm
  rw [hcomm]
  exact (Formula.interp_update_fresh_bool κ r.fmla x vb
          (ρ.update b nuName v) hxfv hxn).symm

/-- Convert `x ∉ s.fv` and `x ≠ nuName` into `x ∉` the underlying refinement's
    `fmla.fv` (the unfiltered set). -/
private theorem Ty.refine_fmla_fresh_of_fresh {b : Base} {r : Refinement b}
    {x : EVar} (hxfv : x ∉ (Ty.refine b r).fv) (hxν : x ≠ nuName) :
    x ∉ r.fmla.fv := by
  intro hmem
  apply hxfv
  simp [Ty.fv, Refinement.fv, List.mem_filter]
  exact ⟨hmem, hxν⟩

/-- The transport `ρ ↦ ρ updated at x with arbitrary values at both bases`
    preserves `ModelsEnv` for environments where `x` does not appear among
    the dom, type free-vars, or type named binders. -/
private theorem ModelsEnv.transport_to_x
    {κ : KEnv} {Γ : TEnv} {ρ : REnv} {x : EVar} {vi : Int} {vb : Bool}
    (hxd : x ∉ Γ.dom) (hxfv : x ∉ TEnv.tyFv Γ) (hxn : x ∉ TEnv.tyNamed Γ)
    (hxν : x ≠ nuName) (hΓ : ModelsEnv κ ρ Γ) :
    ModelsEnv κ ((ρ.update .int x vi).update .bool x vb) Γ := by
  induction Γ with
  | nil => simp [ModelsEnv]
  | cons hd tl ih =>
    obtain ⟨z, t⟩ := hd
    simp only [TEnv.dom, List.mem_cons, not_or] at hxd
    simp only [TEnv.tyFv, List.mem_append, not_or] at hxfv
    simp only [TEnv.tyNamed, List.mem_append, not_or] at hxn
    have hxz : z ≠ x := fun h => hxd.1 h.symm
    cases t with
    | refine b r =>
      simp only [ModelsEnv] at hΓ ⊢
      have htfv : x ∉ r.fmla.fv :=
        Ty.refine_fmla_fresh_of_fresh hxfv.1 hxν
      have htn : x ∉ r.fmla.named := hxn.1
      have hgetEq : REnv.get b ((ρ.update .int x vi).update .bool x vb) z
                  = REnv.get b ρ z := by
        cases b <;>
          simp [REnv.get, REnv.update, beq_eq_false_iff_ne.mpr (Ne.symm hxz)]
      refine ⟨?_, ih hxd.2 hxfv.2 hxn.2 hΓ.2⟩
      rw [hgetEq]
      rw [Refinement.interp_invariant_under_bool_update r x vb _ _ htfv htn hxν,
          Refinement.interp_invariant_under_int_update r x vi _ _ htfv htn hxν]
      exact hΓ.1
    | arrow s₁ s₂ =>
      simp only [ModelsEnv] at hΓ ⊢
      exact ih hxd.2 hxfv.2 hxn.2 hΓ

/-- `Refinement.subImp` distributes over `replaceFVar` provided `x ≠ nuName`. -/
private theorem Refinement.subImp_replaceFVar {b : Base} (r₁ r₂ : Refinement b)
    (x y : EVar) (hxν : x ≠ nuName) :
    (r₁.subImp r₂).replaceFVar x y =
    (r₁.replaceFVar x y).subImp (r₂.replaceFVar x y) := by
  cases b <;> simp [Refinement.subImp, Formula.replaceFVar,
                    Refinement.replaceFVar, if_neg (Ne.symm hxν)]

/-- Extract the unique refinement from a `Ty.openVar 0 x t = .refine b r`
    equation: the underlying refinement of `t` (when `t` is a refine) has its
    `fmla` related to `r.fmla` via two openBVars at level 0. -/
private theorem Ty.openVar_refine_fmla_eq
    {x : EVar} {b : Base} {r : Refinement b} {t : Ty}
    (h : Ty.openVar 0 x t = .refine b r) :
    ∃ r₀ : Refinement b,
      t = .refine b r₀ ∧
      r.fmla = (r₀.fmla.openBVar .int 0 x).openBVar .bool 0 x := by
  cases t with
  | refine b' r₀ =>
    simp only [Ty.openVar, Refinement.openBVar] at h
    cases h
    exact ⟨r₀, rfl, rfl⟩
  | arrow _ _ => simp [Ty.openVar] at h

theorem entail_f_replace {κ : KEnv} {b : Base} {r₁ r₂ : Refinement b}
    {Γ : TEnv} {s t₁ t₂ : Ty} {x y : EVar}
    (hx : x ∉ Γ.dom ++ s.fv ++ t₁.fv ++ t₂.fv
          ++ Ty.named s ++ Ty.named t₁ ++ Ty.named t₂
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (hy : y ∉ Γ.dom ++ s.fv ++ t₁.fv ++ t₂.fv
          ++ Ty.named s ++ Ty.named t₁ ++ Ty.named t₂
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (ht1 : Ty.openVar 0 x t₁ = Ty.refine b r₁)
    (ht2 : Ty.openVar 0 x t₂ = Ty.refine b r₂) :
    EntailF κ ((x, s) :: Γ) (r₁.subImp r₂) →
    EntailF κ ((y, s) :: Γ) ((r₁.replaceFVar x y).subImp (r₂.replaceFVar x y)) := by
  intro hH
  simp only [List.mem_append, List.mem_singleton, not_or] at hx hy
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxΓd, hxsfv⟩, _hxt1fv⟩, _hxt2fv⟩, hxsn⟩, hxt1n⟩, hxt2n⟩, hxΓfv⟩, hxΓn⟩, hxν⟩ := hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hyΓd, hysfv⟩, _hyt1fv⟩, _hyt2fv⟩, hysn⟩, hyt1n⟩, hyt2n⟩, hyΓfv⟩, hyΓn⟩, hyν⟩ := hy
  intro ρ' hΓ'
  -- Establish that r₁.fmla.binderNames = (original r₀).fmla.binderNames.
  obtain ⟨r₀₁, ht1_eq, hr1_fmla⟩ := Ty.openVar_refine_fmla_eq ht1
  obtain ⟨r₀₂, ht2_eq, hr2_fmla⟩ := Ty.openVar_refine_fmla_eq ht2
  -- Then binderNames of r₁.fmla = binderNames of r₀₁.fmla (preservation through openBVar).
  have hxBn1 : x ∉ r₁.fmla.binderNames := by
    rw [hr1_fmla, Formula.binderNames_openBVar, Formula.binderNames_openBVar]
    intro h
    apply hxt1n
    rw [ht1_eq]; simp [Ty.named]
    exact Formula.binderNames_subset_named _ x h
  have hyBn1 : y ∉ r₁.fmla.binderNames := by
    rw [hr1_fmla, Formula.binderNames_openBVar, Formula.binderNames_openBVar]
    intro h
    apply hyt1n
    rw [ht1_eq]; simp [Ty.named]
    exact Formula.binderNames_subset_named _ y h
  have hxBn2 : x ∉ r₂.fmla.binderNames := by
    rw [hr2_fmla, Formula.binderNames_openBVar, Formula.binderNames_openBVar]
    intro h
    apply hxt2n
    rw [ht2_eq]; simp [Ty.named]
    exact Formula.binderNames_subset_named _ x h
  have hyBn2 : y ∉ r₂.fmla.binderNames := by
    rw [hr2_fmla, Formula.binderNames_openBVar, Formula.binderNames_openBVar]
    intro h
    apply hyt2n
    rw [ht2_eq]; simp [Ty.named]
    exact Formula.binderNames_subset_named _ y h
  -- Define the transported environment ρ = ρ' with x's slots set to y's values.
  let ρ : REnv := (ρ'.update .int x (ρ'.ints y)).update .bool x (ρ'.bools y)
  -- Build ModelsEnv κ ρ ((x, s) :: Γ).
  have hΓρ : ModelsEnv κ ρ ((x, s) :: Γ) := by
    cases s with
    | refine bs rs =>
      simp only [ModelsEnv]
      have hxs_fv : x ∉ rs.fmla.fv := Ty.refine_fmla_fresh_of_fresh hxsfv hxν
      have hΓ_y : Refinement.interp κ rs ρ' (REnv.get bs ρ' y) := hΓ'.1
      have hgetEq : REnv.get bs ρ x = REnv.get bs ρ' y := by
        cases bs <;> simp [ρ, REnv.get, REnv.update]
      refine ⟨?_, ModelsEnv.transport_to_x hxΓd hxΓfv hxΓn hxν hΓ'.2⟩
      rw [hgetEq]
      show Refinement.interp κ rs ((ρ'.update .int x (ρ'.ints y)).update .bool x (ρ'.bools y))
           (REnv.get bs ρ' y)
      rw [Refinement.interp_invariant_under_bool_update rs x _ _ _ hxs_fv hxsn hxν,
          Refinement.interp_invariant_under_int_update rs x _ _ _ hxs_fv hxsn hxν]
      exact hΓ_y
    | arrow _ _ =>
      simp only [ModelsEnv] at hΓ' ⊢
      exact ModelsEnv.transport_to_x hxΓd hxΓfv hxΓn hxν hΓ'
  -- Apply hH to ρ.
  have hinterp : Formula.interp κ ρ (r₁.subImp r₂) := hH ρ hΓρ
  -- Pull the subImp under replaceFVar.
  rw [← Refinement.subImp_replaceFVar r₁ r₂ x y hxν]
  -- The whole subImp's binderNames: nuName plus r₁ and r₂ binderNames.
  have hxBnSub : x ∉ Formula.binderNames (r₁.subImp r₂) := by
    cases b with
    | int  =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      refine ⟨fun h => hxν h, ?_, ?_⟩
      · exact hxBn1
      · exact hxBn2
    | bool =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      refine ⟨fun h => hxν h, ?_, ?_⟩
      · exact hxBn1
      · exact hxBn2
  have hyBnSub : y ∉ Formula.binderNames (r₁.subImp r₂) := by
    cases b with
    | int  =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      refine ⟨fun h => hyν h, ?_, ?_⟩
      · exact hyBn1
      · exact hyBn2
    | bool =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      refine ⟨fun h => hyν h, ?_, ?_⟩
      · exact hyBn1
      · exact hyBn2
  -- Now interp_replaceFVar gives the transport.
  show Formula.interp κ ρ' ((r₁.subImp r₂).replaceFVar x y)
  exact (Formula.interp_replaceFVar κ (r₁.subImp r₂) x y ρ' hxBnSub hyBnSub).mpr hinterp

/-! ## TEnv-level rename infrastructure (for `Subtyp.rename_general`) -/

namespace STLC

/-- Pointwise rename of all binding types in a `TEnv`. Binding *names* are
    preserved (callers ensure freshness so they never equal `x` or `y`). -/
def TEnv.replaceFVar (x y : EVar) : TEnv → TEnv
  | []          => []
  | (z, t) :: Γ => (z, t.replaceFVar x y) :: TEnv.replaceFVar x y Γ

@[simp]
theorem TEnv.replaceFVar_nil (x y : EVar) :
    TEnv.replaceFVar x y ([] : TEnv) = [] := rfl

@[simp]
theorem TEnv.replaceFVar_cons (x y z : EVar) (t : Ty) (Γ : TEnv) :
    TEnv.replaceFVar x y ((z, t) :: Γ) = (z, t.replaceFVar x y) :: TEnv.replaceFVar x y Γ := rfl

@[simp]
theorem TEnv.dom_replaceFVar (x y : EVar) (Γ : TEnv) :
    TEnv.dom (TEnv.replaceFVar x y Γ) = TEnv.dom Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨_, _⟩ := hd
    simp [TEnv.replaceFVar, TEnv.dom, ih]

@[simp]
theorem TEnv.replaceFVar_append (x y : EVar) (Δ Γ : TEnv) :
    TEnv.replaceFVar x y (Δ ++ Γ) =
      TEnv.replaceFVar x y Δ ++ TEnv.replaceFVar x y Γ := by
  induction Δ with
  | nil => rfl
  | cons hd tl ih => obtain ⟨_, _⟩ := hd; simp [TEnv.replaceFVar, ih]

/-! ## Helpers re-proved (the upstream ones are `private`) -/

/-- Positive subset: every fv of `t.openBVar b' k z` is either `z` or in fv of `t`. -/
theorem Term.fv_openBVar_subset_pub {b : Base} (b' : Base) (k : Nat) (z : EVar)
    (t : Term b) : ∀ y ∈ Term.fv (t.openBVar b' k z), y = z ∨ y ∈ Term.fv t := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.fv]
  | bvar b'' j =>
    intro y hy
    cases b'' <;> cases b' <;> simp only [Term.openBVar, Term.fv] at hy ⊢ <;>
      (try (split at hy <;> simp_all [Term.fv]))
  | fvar b'' w =>
    intro y hy
    cases b'' <;> simp_all [Term.openBVar, Term.fv]
  | add t₁ t₂ ih₁ ih₂ =>
    intro y hy
    simp only [Term.openBVar, Term.fv, List.mem_append] at hy ⊢
    rcases hy with h | h
    · rcases ih₁ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases ih₂ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
  | not t ih => simp only [Term.openBVar, Term.fv]; exact ih
  | and t₁ t₂ ih₁ ih₂ =>
    intro y hy
    simp only [Term.openBVar, Term.fv, List.mem_append] at hy ⊢
    rcases hy with h | h
    · rcases ih₁ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases ih₂ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')

/-- `x ∉ φ.named` and `x ≠ z` imply `x ∉ (φ.openBVar b k z).named`. -/
theorem Formula.named_openBVar_not_mem_pub (φ : Formula) (b : Base) (k : Nat)
    (z x : EVar) (hx : x ∉ φ.named) (hxz : x ≠ z) :
    x ∉ (φ.openBVar b k z).named := by
  induction φ generalizing k with
  | tt | ff | eqI _ _ | eqB _ _ | leqI _ _ => simp [Formula.openBVar, Formula.named]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.openBVar, Formula.named, List.mem_append, not_or] at *
    exact ⟨ih₁ k hx.1, ih₂ k hx.2⟩
  | not φ ih => simp [Formula.openBVar, Formula.named] at *; exact ih k hx
  | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
    simp only [Formula.openBVar, Formula.named, List.mem_cons, not_or] at *
    exact ⟨hx.1, ih k hx.2⟩
  | kapp name args =>
    simp only [Formula.openBVar, Formula.named, List.mem_flatMap, List.mem_map] at hx ⊢
    rintro ⟨_, ⟨a₀, ha₀_mem, rfl⟩, hx_in⟩
    apply hx
    refine ⟨a₀, ha₀_mem, ?_⟩
    have hx_in' : x ∈ (a₀.snd.openBVar b k z).fv := hx_in
    rcases Term.fv_openBVar_subset_pub b k z a₀.2 x hx_in' with hz | hin
    · exact absurd hz hxz
    · exact hin

/-! ## Commuting open/replace at a *different* name (z ≠ x, y) -/

/-- Opening a term at a name `z` different from both `x` and `y` commutes with
    renaming `x → y`. (Contrast `Term.openBVar_replaceFVar_chain`, which opens
    at `x` itself.) -/
theorem Term.openBVar_replaceFVar_comm_other {b' b : Base} (k : Nat) (x y z : EVar)
    (hxz : x ≠ z) (t : Term b) :
    (t.openBVar b' k z).replaceFVar x y =
    (t.replaceFVar x y).openBVar b' k z := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.replaceFVar]
  | bvar b'' j =>
    cases b'' <;> cases b' <;>
      simp only [Term.openBVar, Term.replaceFVar] <;>
      (try (split <;> simp_all [Term.replaceFVar, Ne.symm hxz]))
  | fvar b'' w =>
    by_cases hwx : w = x <;>
      cases b'' <;>
      simp_all [Term.openBVar, Term.replaceFVar]
  | add t₁ t₂ ih₁ ih₂ => simp [Term.openBVar, Term.replaceFVar, ih₁, ih₂]
  | not t ih          => simp [Term.openBVar, Term.replaceFVar, ih]
  | and t₁ t₂ ih₁ ih₂ => simp [Term.openBVar, Term.replaceFVar, ih₁, ih₂]

theorem Formula.openBVar_replaceFVar_comm_other (b' : Base) (k : Nat) (x y z : EVar)
    (hxz : x ≠ z) (φ : Formula) (hxbn : x ∉ φ.binderNames) :
    (φ.openBVar b' k z).replaceFVar x y =
    (φ.replaceFVar x y).openBVar b' k z := by
  induction φ generalizing k with
  | tt | ff => simp [Formula.openBVar, Formula.replaceFVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.openBVar, Formula.replaceFVar,
          Term.openBVar_replaceFVar_comm_other k x y z hxz t₁,
          Term.openBVar_replaceFVar_comm_other k x y z hxz t₂]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.binderNames, List.mem_append, not_or] at hxbn
    simp [Formula.openBVar, Formula.replaceFVar, ih₁ k hxbn.1, ih₂ k hxbn.2]
  | not φ ih =>
    simp only [Formula.binderNames] at hxbn
    simp [Formula.openBVar, Formula.replaceFVar, ih k hxbn]
  | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
    simp only [Formula.binderNames, List.mem_cons, not_or] at hxbn
    have hwx : w ≠ x := fun h => hxbn.1 h.symm
    simp only [Formula.openBVar, Formula.replaceFVar, if_neg hwx, ih k hxbn.2]
  | kapp kname args =>
    simp only [Formula.openBVar, Formula.replaceFVar]
    congr 1
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro ⟨b'', t⟩ _
    show Sigma.mk b'' ((t.openBVar b' k z).replaceFVar x y) =
         Sigma.mk b'' ((t.replaceFVar x y).openBVar b' k z)
    rw [Term.openBVar_replaceFVar_comm_other k x y z hxz t]

theorem Refinement.openBVar_replaceFVar_comm_other {b'' : Base} (b' : Base) (k : Nat)
    (x y z : EVar) (hxz : x ≠ z) (r : Refinement b'') (hxbn : x ∉ r.fmla.binderNames) :
    (r.openBVar b' k z).replaceFVar x y =
    (r.replaceFVar x y).openBVar b' k z := by
  obtain ⟨fmla⟩ := r
  show (⟨_⟩ : Refinement b'') = ⟨_⟩
  congr 1
  exact Formula.openBVar_replaceFVar_comm_other b' k x y z hxz fmla hxbn

/-- The "binder names" of a `Ty`: just the existential/universal binder names
    inside refinements (recursively into arrows). Unlike `Ty.named`, this
    excludes kapp argument fvs, so it is invariant under `Ty.openVar`. -/
def Ty.binderNames : Ty → List EVar
  | .refine _ r => r.fmla.binderNames
  | .arrow s t  => s.binderNames ++ t.binderNames

theorem Ty.binderNames_subset_named (t : Ty) :
    ∀ x ∈ Ty.binderNames t, x ∈ Ty.named t := by
  induction t with
  | refine b r =>
    intro x h
    simp only [Ty.binderNames] at h
    simp only [Ty.named]
    exact Formula.binderNames_subset_named _ x h
  | arrow s t ihs iht =>
    intro x h
    simp only [Ty.binderNames, List.mem_append] at h
    simp only [Ty.named, List.mem_append]
    rcases h with h | h
    · exact Or.inl (ihs x h)
    · exact Or.inr (iht x h)

@[simp]
theorem Ty.binderNames_openVar (t : Ty) (k : Nat) (z : EVar) :
    Ty.binderNames (t.openVar k z) = Ty.binderNames t := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.openVar, Ty.binderNames, Refinement.openBVar]
    rw [Formula.binderNames_openBVar, Formula.binderNames_openBVar]
  | arrow s t ihs iht =>
    simp [Ty.openVar, Ty.binderNames, ihs k, iht (k+1)]

/-- Opening a type at a name `z ≠ x` commutes with renaming `x → y`.
    Requires only `x ∉ Ty.binderNames t` (not the stronger `x ∉ Ty.named t`),
    because binder names are invariant under openBVar (kapp args contribute
    fv but not binderNames). -/
theorem Ty.replaceFVar_openVar_comm (t : Ty) (k : Nat) (z x y : EVar)
    (hxz : x ≠ z) (hxbn : x ∉ Ty.binderNames t) :
    (t.openVar k z).replaceFVar x y = (t.replaceFVar x y).openVar k z := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.binderNames] at hxbn
    simp only [Ty.openVar, Ty.replaceFVar]
    -- chain through bool then int; binderNames is invariant under openBVar so x ∉ binderNames persists.
    have hxn_int : x ∉ (r.openBVar .int k z).fmla.binderNames := by
      obtain ⟨φ⟩ := r
      simp only [Refinement.openBVar, Formula.binderNames_openBVar]
      exact hxbn
    rw [Refinement.openBVar_replaceFVar_comm_other .bool k x y z hxz _ hxn_int]
    rw [Refinement.openBVar_replaceFVar_comm_other .int k x y z hxz r hxbn]
  | arrow s t ihs iht =>
    simp only [Ty.binderNames, List.mem_append, not_or] at hxbn
    simp [Ty.openVar, Ty.replaceFVar, ihs k hxbn.1, iht (k+1) hxbn.2]

end STLC

/-! ## Generalized rename infrastructure (Δ prefix) -/

namespace STLC

/-- ρ updated at `x` to carry `y`'s slot values. -/
@[simp]
def REnv.swap_x (ρ : REnv) (x y : EVar) : REnv :=
  (ρ.update .int x (ρ.ints y)).update .bool x (ρ.bools y)

/-- Swap commutes with a `ν`-update, provided neither `x` nor `y` is `ν`. -/
private theorem REnv.swap_x_update_nu (b : Base) (ρ : REnv) (x y : EVar)
    (v : b.interp) (hxν : x ≠ nuName) (hyν : y ≠ nuName) :
    (REnv.swap_x ρ x y).update b nuName v
      = REnv.swap_x (ρ.update b nuName v) x y := by
  have hxν' : ¬(nuName = x) := fun h => hxν h.symm
  have hyν' : ¬(nuName = y) := fun h => hyν h.symm
  apply REnv.ext <;> funext z <;> cases b <;>
    simp only [REnv.swap_x, REnv.update] <;>
    (by_cases hxz : x = z) <;>
    (first | (subst hxz; simp [hxν', hyν', hxν.symm])
           | (by_cases hνz : nuName = z
              · subst hνz; simp [hxz, hyν']
              · simp [hxz, hνz]))

/-- Rename keystone: interpreting the renamed refinement at ρ equals
    interpreting the original at the swap. -/
private theorem Refinement.interp_replaceFVar_bridge
    {κ : KEnv} {b : Base} (r : Refinement b)
    (x y : EVar) (ρ : REnv) (v : b.interp)
    (hxbn : x ∉ r.fmla.binderNames) (hybn : y ∉ r.fmla.binderNames)
    (hxν : x ≠ nuName) (hyν : y ≠ nuName) :
    Refinement.interp κ (r.replaceFVar x y) ρ v ↔
    Refinement.interp κ r (REnv.swap_x ρ x y) v := by
  simp only [Refinement.interp, Refinement.replaceFVar]
  rw [Formula.interp_replaceFVar κ r.fmla x y _ hxbn hybn,
      REnv.swap_x_update_nu b ρ x y v hxν hyν]
  rfl

/-- Per-binding `binderNames` of refine entries in a `TEnv`. Arrow bindings
    contribute nothing (they have no associated formula). -/
def TEnv.tyBinderNames : TEnv → List EVar
  | []                       => []
  | (_, .refine _ r) :: Γ    => r.fmla.binderNames ++ TEnv.tyBinderNames Γ
  | (_, .arrow _ _)  :: Γ    => TEnv.tyBinderNames Γ

theorem TEnv.tyBinderNames_subset_tyNamed (Γ : TEnv) :
    ∀ x ∈ TEnv.tyBinderNames Γ, x ∈ TEnv.tyNamed Γ := by
  induction Γ with
  | nil => intro x h; simp [TEnv.tyBinderNames] at h
  | cons hd tl ih =>
    obtain ⟨z, t⟩ := hd
    intro x h
    cases t with
    | refine b r =>
      simp only [TEnv.tyBinderNames, List.mem_append] at h
      simp only [TEnv.tyNamed, Ty.named, List.mem_append]
      rcases h with h | h
      · exact Or.inl (Formula.binderNames_subset_named _ x h)
      · exact Or.inr (ih x h)
    | arrow _ _ =>
      simp only [TEnv.tyBinderNames] at h
      simp only [TEnv.tyNamed, Ty.named, List.mem_append]
      exact Or.inr (ih x h)

/-- ModelsEnv transport: ρ models the renamed `Δ ++ (y, s) :: Γ` implies
    `swap_x ρ x y` models the original `Δ ++ (x, s) :: Γ`. -/
private theorem ModelsEnv.replaceFVar_to_swap
    {κ : KEnv} (Δ Γ : TEnv) (s : Ty) (x y : EVar) (ρ : REnv)
    -- x freshness: x is fresh in the deep Γ (but may appear in Δ types — that's why we rename)
    (hxΓdom : x ∉ Γ.dom) (hxsfv : x ∉ s.fv) (hxsn : x ∉ Ty.named s)
    (hxΓfv : x ∉ TEnv.tyFv Γ) (hxΓn : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName)
    -- y is fresh everywhere
    (hyΔdom : y ∉ TEnv.dom Δ) (hyΔbn : y ∉ TEnv.tyBinderNames Δ)
    (hyν : y ≠ nuName)
    -- x doesn't appear as a binding NAME in Δ (only in types via rename)
    (hxΔdom : x ∉ TEnv.dom Δ) (hxΔbn : x ∉ TEnv.tyBinderNames Δ)
    (h : ModelsEnv κ ρ (TEnv.replaceFVar x y Δ ++ (y, s) :: Γ)) :
    ModelsEnv κ (REnv.swap_x ρ x y) (Δ ++ (x, s) :: Γ) := by
  induction Δ with
  | nil =>
    -- ρ models (y, s) :: Γ; need swap_x ρ models (x, s) :: Γ
    simp only [TEnv.replaceFVar, List.nil_append] at h
    simp only [List.nil_append]
    cases s with
    | refine bs rs =>
      simp only [ModelsEnv] at h ⊢
      obtain ⟨hint_y, hΓ⟩ := h
      refine ⟨?_, ?_⟩
      · -- Refinement.interp κ rs (swap_x ρ x y) (get bs (swap_x ρ x y) x) — equals get bs ρ y
        have hgetEq : REnv.get bs (REnv.swap_x ρ x y) x = REnv.get bs ρ y := by
          cases bs <;> simp [REnv.swap_x, REnv.get, REnv.update]
        rw [hgetEq]
        -- Need Refinement.interp κ rs (swap_x ρ x y) (get bs ρ y), given hint_y at ρ.
        have hxs_fv : x ∉ rs.fmla.fv := Ty.refine_fmla_fresh_of_fresh hxsfv hxν
        -- swap_x ρ x y is just ρ with x's slots overwritten. Refinement.interp at fresh-x ρ is invariant.
        show Refinement.interp κ rs (REnv.swap_x ρ x y) (REnv.get bs ρ y)
        simp only [REnv.swap_x]
        rw [Refinement.interp_invariant_under_bool_update rs x _ _ _ hxs_fv hxsn hxν,
            Refinement.interp_invariant_under_int_update rs x _ _ _ hxs_fv hxsn hxν]
        exact hint_y
      · -- Need ModelsEnv κ (swap_x ρ x y) Γ from ModelsEnv κ ρ Γ via transport_to_x
        exact ModelsEnv.transport_to_x hxΓdom hxΓfv hxΓn hxν hΓ
    | arrow _ _ =>
      simp only [ModelsEnv] at h ⊢
      exact ModelsEnv.transport_to_x hxΓdom hxΓfv hxΓn hxν h
  | cons hd tl ih =>
    obtain ⟨z, t⟩ := hd
    simp only [TEnv.replaceFVar, List.cons_append] at h
    simp only [TEnv.dom, List.mem_cons, not_or] at hxΔdom hyΔdom
    simp only [List.cons_append]
    cases t with
    | refine bt rt =>
      simp only [ModelsEnv] at h ⊢
      obtain ⟨hint, hΓ'tl⟩ := h
      simp only [TEnv.tyBinderNames, List.mem_append, not_or] at hxΔbn hyΔbn
      refine ⟨?_, ?_⟩
      · -- ρ satisfies (z, rt.replaceFVar). Need swap_x ρ satisfies (z, rt).
        have hzx : x ≠ z := hxΔdom.1
        have hzy : y ≠ z := hyΔdom.1
        have hgetEq : REnv.get bt (REnv.swap_x ρ x y) z = REnv.get bt ρ z := by
          cases bt <;> simp [REnv.swap_x, REnv.get, REnv.update] <;>
            intro h <;> exact (hzx h).elim
        rw [hgetEq]
        -- bridge
        exact (Refinement.interp_replaceFVar_bridge rt x y ρ (REnv.get bt ρ z)
                 hxΔbn.1 hyΔbn.1 hxν hyν).mp hint
      · exact ih hyΔdom.2 hyΔbn.2 hxΔdom.2 hxΔbn.2 hΓ'tl
    | arrow _ _ =>
      simp only [ModelsEnv] at h ⊢
      simp only [TEnv.tyBinderNames] at hxΔbn hyΔbn
      exact ih hyΔdom.2 hyΔbn hxΔdom.2 hxΔbn h

/-- The generalized refine-step: `EntailF` transports through a `Δ`-prefixed
    rename, where `Δ` may mention `x` (renamed pointwise) but neither `Δ` nor
    the deep `Γ` mentions `y`. -/
theorem entail_f_replace_general {κ : KEnv} {b : Base} (r₁ r₂ : Refinement b)
    (Δ Γ : TEnv) (s : Ty) (x y : EVar)
    (hxΓdom : x ∉ Γ.dom) (hxsfv : x ∉ s.fv) (hxsn : x ∉ Ty.named s)
    (hxΓfv : x ∉ TEnv.tyFv Γ) (hxΓn : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName)
    (hyν : y ≠ nuName)
    (hxΔdom : x ∉ TEnv.dom Δ) (hxΔbn : x ∉ TEnv.tyBinderNames Δ)
    (hyΔdom : y ∉ TEnv.dom Δ) (hyΔbn : y ∉ TEnv.tyBinderNames Δ)
    (hxr₁bn : x ∉ r₁.fmla.binderNames) (hxr₂bn : x ∉ r₂.fmla.binderNames)
    (hyr₁bn : y ∉ r₁.fmla.binderNames) (hyr₂bn : y ∉ r₂.fmla.binderNames)
    (hent : EntailF κ (Δ ++ (x, s) :: Γ) (Refinement.subImp r₁ r₂)) :
    EntailF κ (TEnv.replaceFVar x y Δ ++ (y, s) :: Γ)
              (Refinement.subImp (r₁.replaceFVar x y) (r₂.replaceFVar x y)) := by
  intro ρ hΓρ
  -- Transport ρ to swap_x ρ x y, which models the original.
  have hΓ' : ModelsEnv κ (REnv.swap_x ρ x y) (Δ ++ (x, s) :: Γ) :=
    ModelsEnv.replaceFVar_to_swap Δ Γ s x y ρ hxΓdom hxsfv hxsn hxΓfv hxΓn hxν
      hyΔdom hyΔbn hyν hxΔdom hxΔbn hΓρ
  -- Apply hent.
  have hi : Formula.interp κ (REnv.swap_x ρ x y) (Refinement.subImp r₁ r₂) :=
    hent (REnv.swap_x ρ x y) hΓ'
  -- Transport back to ρ via Formula.interp_replaceFVar.
  rw [← Refinement.subImp_replaceFVar r₁ r₂ x y hxν]
  -- Need binderNames freshness on subImp.
  have hxBnSub : x ∉ Formula.binderNames (r₁.subImp r₂) := by
    cases b with
    | int  =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      exact ⟨fun h => hxν h, hxr₁bn, hxr₂bn⟩
    | bool =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      exact ⟨fun h => hxν h, hxr₁bn, hxr₂bn⟩
  have hyBnSub : y ∉ Formula.binderNames (r₁.subImp r₂) := by
    cases b with
    | int  =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      exact ⟨fun h => hyν h, hyr₁bn, hyr₂bn⟩
    | bool =>
      simp only [Refinement.subImp, Formula.binderNames, List.mem_cons,
                 List.mem_append, not_or]
      exact ⟨fun h => hyν h, hyr₁bn, hyr₂bn⟩
  exact (Formula.interp_replaceFVar κ (r₁.subImp r₂) x y ρ hxBnSub hyBnSub).mpr hi

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

end STLC

/-- The generalized rename: rename `x → y` in `Δ ++ (x, s) :: Γ`, where the
    types `t₁` and `t₂` may mention `x`. The arrow case's recursive call
    extends `Δ` with the freshly-chosen `(z, …)` binding.

    Proved by `induction h`, with the motive parametric over the `Δ` prefix
    (introduced via `intros` in each case). -/
theorem Subtyp.rename_general {κ : KEnv} {Γall : TEnv} {t₁ t₂ : Ty}
    (h : Subtyp κ Γall t₁ t₂) :
    ∀ (Δ Γ : TEnv) (s : Ty) (x y : EVar)
      (hΓall : Γall = Δ ++ (x, s) :: Γ)
      (hxΓdom : x ∉ Γ.dom) (hxsfv : x ∉ s.fv) (hxsn : x ∉ Ty.named s)
      (hxΓfv : x ∉ TEnv.tyFv Γ) (hxΓn : x ∉ TEnv.tyNamed Γ) (hxν : x ≠ nuName)
      (hxΔdom : x ∉ TEnv.dom Δ) (hxΔbn : x ∉ TEnv.tyBinderNames Δ)
      (hyΓdom : y ∉ Γ.dom) (hysfv : y ∉ s.fv) (hysn : y ∉ Ty.named s)
      (hyΓfv : y ∉ TEnv.tyFv Γ) (hyΓn : y ∉ TEnv.tyNamed Γ) (hyν : y ≠ nuName)
      (hyΔdom : y ∉ TEnv.dom Δ) (hyΔbn : y ∉ TEnv.tyBinderNames Δ)
      (hyΔfv : y ∉ TEnv.tyFv Δ) (hyΔn : y ∉ TEnv.tyNamed Δ)
      (hyt₁ : y ∉ t₁.fv) (hyt₁n : y ∉ Ty.named t₁)
      (hyt₂ : y ∉ t₂.fv) (hyt₂n : y ∉ Ty.named t₂)
      (hxt₁bn : x ∉ Ty.binderNames t₁) (hxt₂bn : x ∉ Ty.binderNames t₂),
      Subtyp κ (TEnv.replaceFVar x y Δ ++ (y, s) :: Γ)
              (t₁.replaceFVar x y) (t₂.replaceFVar x y) := by
  induction h with
  | refine hent =>
    rename_i b r₁ r₂  -- grab b, r₁, r₂ (κ', Γ' are inferred from outer context)
    intro Δ Γ s x y hΓall hxΓdom hxsfv hxsn hxΓfv hxΓn hxν
          hxΔdom hxΔbn hyΓdom hysfv hysn hyΓfv hyΓn hyν hyΔdom hyΔbn hyΔfv hyΔn
          hyt₁ hyt₁n hyt₂ hyt₂n hxt₁bn hxt₂bn
    subst hΓall
    -- For refine, x ∉ Ty.binderNames (.refine b r) = r.fmla.binderNames directly.
    have hxr₁bn : x ∉ r₁.fmla.binderNames := hxt₁bn
    have hxr₂bn : x ∉ r₂.fmla.binderNames := hxt₂bn
    have hyr₁bn : y ∉ r₁.fmla.binderNames := by
      intro h; apply hyt₁n; simp only [Ty.named]
      exact Formula.binderNames_subset_named _ y h
    have hyr₂bn : y ∉ r₂.fmla.binderNames := by
      intro h; apply hyt₂n; simp only [Ty.named]
      exact Formula.binderNames_subset_named _ y h
    apply Subtyp.refine
    exact entail_f_replace_general r₁ r₂ Δ Γ s x y
            hxΓdom hxsfv hxsn hxΓfv hxΓn hxν hyν
            hxΔdom hxΔbn hyΔdom hyΔbn
            hxr₁bn hxr₂bn hyr₁bn hyr₂bn hent
  | arrow L hsubs hf ih_sub ih_cof =>
    rename_i s₁ t₁' s₂ t₂'
    intro Δ Γ s x y hΓall hxΓdom hxsfv hxsn hxΓfv hxΓn hxν
          hxΔdom hxΔbn hyΓdom hysfv hysn hyΓfv hyΓn hyν hyΔdom hyΔbn hyΔfv hyΔn
          hyt₁ hyt₁n hyt₂ hyt₂n hxt₁bn hxt₂bn
    subst hΓall
    -- Decompose: arrow's named/fv/binderNames split into halves.
    simp only [Ty.fv, Ty.named, List.mem_append, not_or] at hyt₁ hyt₁n hyt₂ hyt₂n
    simp only [Ty.binderNames, List.mem_append, not_or] at hxt₁bn hxt₂bn
    -- Massive fresh-var L'.
    apply Subtyp.arrow (L := L ++ TEnv.dom Δ ++ Γ.dom ++ [x] ++ [y] ++ [nuName] ++
                              TEnv.tyFv Δ ++ TEnv.tyNamed Δ ++ TEnv.tyBinderNames Δ ++
                              TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++
                              s₁.fv ++ s₂.fv ++ Ty.fv t₁' ++ Ty.fv t₂' ++
                              Ty.named s₁ ++ Ty.named s₂ ++ Ty.named t₁' ++ Ty.named t₂' ++
                              s.fv ++ Ty.named s)
    · -- Input contravariance
      exact ih_sub Δ Γ s x y rfl hxΓdom hxsfv hxsn hxΓfv hxΓn hxν
              hxΔdom hxΔbn hyΓdom hysfv hysn hyΓfv hyΓn hyν hyΔdom hyΔbn hyΔfv hyΔn
              hyt₂.1 hyt₂n.1 hyt₁.1 hyt₁n.1 hxt₂bn.1 hxt₁bn.1
    · -- Codomain via IH at extended Δ'
      intro z hz
      simp only [List.mem_append, List.mem_singleton, not_or] at hz
      -- Extract each freshness fact via grind on the bundled hz.
      have hzL : z ∉ L := by grind
      have hzΔdom : z ∉ TEnv.dom Δ := by grind
      have hzΓdom : z ∉ Γ.dom := by grind
      have hzx : z ≠ x := by grind
      have hzy : z ≠ y := by grind
      have hzν : z ≠ nuName := by grind
      have hzΔfv : z ∉ TEnv.tyFv Δ := by grind
      have hzΔn : z ∉ TEnv.tyNamed Δ := by grind
      have hzΔbn : z ∉ TEnv.tyBinderNames Δ := by grind
      have hzΓfv : z ∉ TEnv.tyFv Γ := by grind
      have hzΓn : z ∉ TEnv.tyNamed Γ := by grind
      have hzs2fv : z ∉ s₂.fv := by grind
      have hzt1fv : z ∉ Ty.fv t₁' := by grind
      have hzt2fv : z ∉ Ty.fv t₂' := by grind
      have hzs2n : z ∉ Ty.named s₂ := by grind
      have hzt1n : z ∉ Ty.named t₁' := by grind
      have hzt2n : z ∉ Ty.named t₂' := by grind
      -- x ∉ TEnv.tyBinderNames ((z, s₂) :: Δ) follows from hxt₂bn.1 and hxΔbn.
      have hxΔbn' : x ∉ TEnv.tyBinderNames ((z, s₂) :: Δ) := by
        cases hs₂_eq : s₂ with
        | refine bs rs =>
          simp only [TEnv.tyBinderNames, List.mem_append, not_or]
          refine ⟨?_, hxΔbn⟩
          have : x ∉ Ty.binderNames (.refine bs rs) := hs₂_eq ▸ hxt₂bn.1
          exact this
        | arrow _ _ => simp only [TEnv.tyBinderNames]; exact hxΔbn
      -- y ∉ TEnv.tyBinderNames ((z, s₂) :: Δ) follows from y ∉ Ty.named s₂ and binderNames ⊆ named.
      have hyΔbn' : y ∉ TEnv.tyBinderNames ((z, s₂) :: Δ) := by
        cases hs₂_eq : s₂ with
        | refine bs rs =>
          simp only [TEnv.tyBinderNames, List.mem_append, not_or]
          refine ⟨?_, hyΔbn⟩
          intro h
          apply hyt₂n.1
          rw [hs₂_eq]; simp only [Ty.named]
          exact Formula.binderNames_subset_named _ y h
        | arrow _ _ => simp only [TEnv.tyBinderNames]; exact hyΔbn
      -- Apply IH at the extended Δ' = (z, s₂) :: Δ.
      have ih := ih_cof z hzL ((z, s₂) :: Δ) Γ s x y rfl
                   hxΓdom hxsfv hxsn hxΓfv hxΓn hxν
                   (by simp [TEnv.dom]; exact ⟨fun h => hzx h.symm, hxΔdom⟩)
                   hxΔbn'
                   hyΓdom hysfv hysn hyΓfv hyΓn hyν
                   (by simp [TEnv.dom]; exact ⟨fun h => hzy h.symm, hyΔdom⟩)
                   hyΔbn'
                   (by simp [TEnv.tyFv]; exact ⟨hyt₂.1, hyΔfv⟩)
                   (by simp [TEnv.tyNamed]; exact ⟨hyt₂n.1, hyΔn⟩)
                   (Ty.fv_openVar_not_mem t₁' 0 z y hyt₁.2 hzy.symm)
                   (Ty.named_openVar_not_mem t₁' 0 z y hyt₁n.2 hzy.symm)
                   (Ty.fv_openVar_not_mem t₂' 0 z y hyt₂.2 hzy.symm)
                   (Ty.named_openVar_not_mem t₂' 0 z y hyt₂n.2 hzy.symm)
                   (by rw [Ty.binderNames_openVar]; exact hxt₁bn.2)
                   (by rw [Ty.binderNames_openVar]; exact hxt₂bn.2)
      -- Convert (t.openVar 0 z).renamed = (t.renamed).openVar 0 z via Ty.replaceFVar_openVar_comm.
      rw [Ty.replaceFVar_openVar_comm t₁' 0 z x y hzx.symm hxt₁bn.2,
          Ty.replaceFVar_openVar_comm t₂' 0 z x y hzx.symm hxt₂bn.2] at ih
      simp only [TEnv.replaceFVar, List.cons_append] at ih
      exact ih

/-- Rename `x → y` at the head of the context for an `openVar`-shaped Subtyp.
    This is the original `Subtyp.rename`, derived from `Subtyp.rename_general`
    by instantiating the prefix `Δ` to `[]` and using `Ty.openVar_replace` to
    match `Ty.openVar 0 y` with `(Ty.openVar 0 x).replaceFVar`. -/
theorem Subtyp.rename {κ : KEnv} {Γ : TEnv} {s t₁ t₂ : Ty} (x y : EVar)
    (hx : x ∉ Γ.dom ++ s.fv ++ t₁.fv ++ t₂.fv
          ++ Ty.named s ++ Ty.named t₁ ++ Ty.named t₂
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (hy : y ∉ Γ.dom ++ s.fv ++ t₁.fv ++ t₂.fv
          ++ Ty.named s ++ Ty.named t₁ ++ Ty.named t₂
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (h : Subtyp κ ((x, s) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x)) :
    Subtyp κ ((y, s) :: Γ) (t₁.openVar 0 y) (t₂.openVar 0 y) := by
  -- If y = x, the rename is the identity.
  by_cases hyx : y = x
  · subst hyx; exact h
  -- Otherwise y ≠ x. Decompose freshness.
  simp only [List.mem_append, List.mem_singleton, not_or] at hx hy
  have hxν : x ≠ nuName := by grind
  have hyν : y ≠ nuName := by grind
  -- Apply Subtyp.rename_general with Δ = [].
  have key := Subtyp.rename_general h [] Γ s x y (by simp)
                (by grind) (by grind) (by grind) (by grind) (by grind) hxν
                (by simp [TEnv.dom]) (by simp [TEnv.tyBinderNames])
                (by grind) (by grind) (by grind) (by grind) (by grind) hyν
                (by simp [TEnv.dom]) (by simp [TEnv.tyBinderNames])
                (by simp [TEnv.tyFv]) (by simp [TEnv.tyNamed])
                (Ty.fv_openVar_not_mem t₁ 0 x y (by grind) hyx)
                (Ty.named_openVar_not_mem t₁ 0 x y (by grind) hyx)
                (Ty.fv_openVar_not_mem t₂ 0 x y (by grind) hyx)
                (Ty.named_openVar_not_mem t₂ 0 x y (by grind) hyx)
                (by rw [Ty.binderNames_openVar]
                    intro h; apply (by grind : x ∉ Ty.named t₁)
                    exact Ty.binderNames_subset_named t₁ x h)
                (by rw [Ty.binderNames_openVar]
                    intro h; apply (by grind : x ∉ Ty.named t₂)
                    exact Ty.binderNames_subset_named t₂ x h)
  -- Convert back: t.openVar 0 y = (t.openVar 0 x).replaceFVar x y
  have hxt1fv : x ∉ t₁.fv := by grind
  have hxt2fv : x ∉ t₂.fv := by grind
  have hxt1n : x ∉ Ty.named t₁ := by grind
  have hxt2n : x ∉ Ty.named t₂ := by grind
  rw [← Ty.openVar_replace 0 x y t₁ hxt1fv hxt1n hxν,
      ← Ty.openVar_replace 0 x y t₂ hxt2fv hxt2n hxν]
  simpa using key

/-! ## Sub alpha-invariance

  The algorithmic `sub` chooses its bound name `w := EVar.fresh (s.fv ∪ t.fv)`
  which doesn't see the typing context `Γ`. To bridge sub's result at this `w`
  to a `z` fresh from `Γ.dom` (needed for `Subtyp.rename` in sub_sound's arrow
  case), we use alpha-conversion invariance of `sub`.

  These lemmas are stated below and the deeper proofs are deferred. Each one
  could be discharged via well-founded recursion on `Ty.skel`, leveraging the
  `REnv.swap_x` infrastructure already built for `Subtyp.rename_general`. -/

/-- Helper: `r_z = r_w.replaceFVar w z` under freshness of `w` in `r.fmla.fv` and named. -/
private theorem Refinement.openVar_alpha {b : Base} (r : Refinement b) (w z : EVar)
    (hwfv : w ∉ r.fmla.fv) (hwn : w ∉ r.fmla.named) :
    ((r.openBVar .int 0 z).openBVar .bool 0 z) =
    (((r.openBVar .int 0 w).openBVar .bool 0 w).replaceFVar w z) := by
  rw [Refinement.openBVar2_replaceFVar_chain 0 w z r hwn,
      Refinement.replaceFVar_id_of_fresh r w z hwfv]

/-- Helper: `binderNames` of a refinement formula is invariant under double openBVar. -/
private theorem Refinement.binderNames_openBVar2 {b : Base} (r : Refinement b)
    (k : Nat) (x : EVar) :
    ((r.openBVar .int k x).openBVar .bool k x).fmla.binderNames = r.fmla.binderNames := by
  obtain ⟨φ⟩ := r
  simp only [Refinement.openBVar, Formula.binderNames_openBVar]

/-- Alpha-conversion of `sub` at openVar opener position.

    Refine cases proved via `Refinement.interp_replaceFVar_bridge`.
    Arrow case **deferred** (requires double alpha-renaming for inner fresh). -/
theorem sub_openVar_alpha (t1 t2 : Ty) (w z : EVar) (c_w : Constraint)
    (hwt1 : w ∉ t1.fv) (hwt2 : w ∉ t2.fv) (hwn1 : w ∉ Ty.named t1) (hwn2 : w ∉ Ty.named t2)
    (hzt1 : z ∉ t1.fv) (hzt2 : z ∉ t2.fv) (hzn1 : z ∉ Ty.named t1) (hzn2 : z ∉ Ty.named t2)
    (hwν : w ≠ nuName) (hzν : z ≠ nuName)
    (h : sub (t1.openVar 0 w) (t2.openVar 0 w) = some c_w) :
    ∃ c_z : Constraint,
      sub (t1.openVar 0 z) (t2.openVar 0 z) = some c_z ∧
      ∀ κ ρ, c_z κ ρ ↔ c_w κ (REnv.swap_x ρ w z) := by
  match t1, t2 with
  | .refine .int r1, .refine .int r2 =>
    simp only [Ty.openVar, sub, Option.some.injEq] at h
    refine ⟨fun κ ρ => ∀ v : Int,
        Refinement.interp κ ((r1.openBVar .int 0 z).openBVar .bool 0 z) ρ v →
        Refinement.interp κ ((r2.openBVar .int 0 z).openBVar .bool 0 z) ρ v,
            by simp only [Ty.openVar, sub], ?_⟩
    intro κ ρ
    have hwfv1 : w ∉ r1.fmla.fv := Ty.refine_fmla_fresh_of_fresh hwt1 hwν
    have hwfv2 : w ∉ r2.fmla.fv := Ty.refine_fmla_fresh_of_fresh hwt2 hwν
    have hwn1' : w ∉ r1.fmla.named := hwn1
    have hwn2' : w ∉ r2.fmla.named := hwn2
    have hzn1' : z ∉ r1.fmla.named := hzn1
    have hzn2' : z ∉ r2.fmla.named := hzn2
    -- r_z = r_w.replaceFVar w z (both r1, r2)
    have ha1 := Refinement.openVar_alpha r1 w z hwfv1 hwn1'
    have ha2 := Refinement.openVar_alpha r2 w z hwfv2 hwn2'
    -- binderNames freshness of r_w (from r1, r2)
    have hwbn1_w : w ∉ ((r1.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hwn1' (Formula.binderNames_subset_named _ _ hb)
    have hzbn1_w : z ∉ ((r1.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hzn1' (Formula.binderNames_subset_named _ _ hb)
    have hwbn2_w : w ∉ ((r2.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hwn2' (Formula.binderNames_subset_named _ _ hb)
    have hzbn2_w : z ∉ ((r2.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hzn2' (Formula.binderNames_subset_named _ _ hb)
    -- Iff for each refinement: R.interp κ r_z ρ v ↔ R.interp κ r_w (swap_x ρ w z) v.
    have iff1 : ∀ v, Refinement.interp κ ((r1.openBVar .int 0 z).openBVar .bool 0 z) ρ v ↔
                     Refinement.interp κ ((r1.openBVar .int 0 w).openBVar .bool 0 w)
                                       (REnv.swap_x ρ w z) v := by
      intro v
      rw [ha1]
      exact Refinement.interp_replaceFVar_bridge _ w z ρ v hwbn1_w hzbn1_w hwν hzν
    have iff2 : ∀ v, Refinement.interp κ ((r2.openBVar .int 0 z).openBVar .bool 0 z) ρ v ↔
                     Refinement.interp κ ((r2.openBVar .int 0 w).openBVar .bool 0 w)
                                       (REnv.swap_x ρ w z) v := by
      intro v
      rw [ha2]
      exact Refinement.interp_replaceFVar_bridge _ w z ρ v hwbn2_w hzbn2_w hwν hzν
    rw [← h]
    simp only []
    -- Goal: (∀ v, R.interp r1_z ρ v → R.interp r2_z ρ v) ↔ (∀ v, R.interp r1_w swap v → R.interp r2_w swap v)
    apply forall_congr'
    intro v
    exact imp_congr (iff1 v) (iff2 v)
  | .refine .bool r1, .refine .bool r2 =>
    simp only [Ty.openVar, sub, Option.some.injEq] at h
    refine ⟨fun κ ρ => ∀ v : Bool,
        Refinement.interp κ ((r1.openBVar .int 0 z).openBVar .bool 0 z) ρ v →
        Refinement.interp κ ((r2.openBVar .int 0 z).openBVar .bool 0 z) ρ v,
            by simp only [Ty.openVar, sub], ?_⟩
    intro κ ρ
    have hwfv1 : w ∉ r1.fmla.fv := Ty.refine_fmla_fresh_of_fresh hwt1 hwν
    have hwfv2 : w ∉ r2.fmla.fv := Ty.refine_fmla_fresh_of_fresh hwt2 hwν
    have hwn1' : w ∉ r1.fmla.named := hwn1
    have hwn2' : w ∉ r2.fmla.named := hwn2
    have hzn1' : z ∉ r1.fmla.named := hzn1
    have hzn2' : z ∉ r2.fmla.named := hzn2
    have ha1 := Refinement.openVar_alpha r1 w z hwfv1 hwn1'
    have ha2 := Refinement.openVar_alpha r2 w z hwfv2 hwn2'
    have hwbn1_w : w ∉ ((r1.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hwn1' (Formula.binderNames_subset_named _ _ hb)
    have hzbn1_w : z ∉ ((r1.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hzn1' (Formula.binderNames_subset_named _ _ hb)
    have hwbn2_w : w ∉ ((r2.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hwn2' (Formula.binderNames_subset_named _ _ hb)
    have hzbn2_w : z ∉ ((r2.openBVar .int 0 w).openBVar .bool 0 w).fmla.binderNames := by
      rw [Refinement.binderNames_openBVar2]
      exact fun hb => hzn2' (Formula.binderNames_subset_named _ _ hb)
    have iff1 : ∀ v, Refinement.interp κ ((r1.openBVar .int 0 z).openBVar .bool 0 z) ρ v ↔
                     Refinement.interp κ ((r1.openBVar .int 0 w).openBVar .bool 0 w)
                                       (REnv.swap_x ρ w z) v := by
      intro v
      rw [ha1]
      exact Refinement.interp_replaceFVar_bridge _ w z ρ v hwbn1_w hzbn1_w hwν hzν
    have iff2 : ∀ v, Refinement.interp κ ((r2.openBVar .int 0 z).openBVar .bool 0 z) ρ v ↔
                     Refinement.interp κ ((r2.openBVar .int 0 w).openBVar .bool 0 w)
                                       (REnv.swap_x ρ w z) v := by
      intro v
      rw [ha2]
      exact Refinement.interp_replaceFVar_bridge _ w z ρ v hwbn2_w hzbn2_w hwν hzν
    rw [← h]
    simp only []
    apply forall_congr'
    intro v
    exact imp_congr (iff1 v) (iff2 v)
  | .refine .int _, .refine .bool _ =>
    simp [sub, Ty.openVar, Refinement.openBVar] at h
  | .refine .bool _, .refine .int _ =>
    simp [sub, Ty.openVar, Refinement.openBVar] at h
  | .refine _ _, .arrow _ _ =>
    simp [sub, Ty.openVar] at h
  | .arrow _ _, .refine _ _ =>
    simp [sub, Ty.openVar] at h
  | .arrow s1 t1', .arrow s2 t2' =>
    -- DEFERRED: requires double alpha-renaming for outer w/z + inner algorithm fresh.
    sorry
  termination_by t1.skel + t2.skel
  decreasing_by all_goals first
    | (simp_wf; simp [Ty.skel]; omega)
    | (simp [Ty.skel]; omega)
    | omega

/-- **DEFERRED**: the high-level wrapper. Given the algorithmic `sub` result
    on an arrow pair and the entailment of its constraint, the codomain
    subtyping holds for any `z` fresh from `Γ` + types + ν. Internally uses
    `sub_openVar_alpha` + `sub_sound` recursion + `Subtyp.rename`. -/
theorem sub_arrow_codomain_sound
    {κ : KEnv} {Γ : TEnv} {s1 t1 s2 t2 : Ty} {c₂ : Constraint} {w : EVar}
    (hc₂ : sub (t1.openVar 0 w) (t2.openVar 0 w) = some c₂)
    (hent_imply : Entail κ Γ (implyBind w s2 c₂ κ))
    (hwt1 : w ∉ t1.fv) (hwt2 : w ∉ t2.fv) (hwn1 : w ∉ Ty.named t1) (hwn2 : w ∉ Ty.named t2)
    (hws2_fv : w ∉ s2.fv) (hws2_n : w ∉ Ty.named s2) (hwν : w ≠ nuName)
    (z : EVar)
    (hzΓdom : z ∉ Γ.dom) (hzs1 : z ∉ s1.fv) (hzs2 : z ∉ s2.fv)
    (hzt1 : z ∉ t1.fv) (hzt2 : z ∉ t2.fv)
    (hzn1 : z ∉ Ty.named t1) (hzn2 : z ∉ Ty.named t2)
    (hzs1n : z ∉ Ty.named s1) (hzs2n : z ∉ Ty.named s2)
    (hzΓfv : z ∉ TEnv.tyFv Γ) (hzΓn : z ∉ TEnv.tyNamed Γ) (hzν : z ≠ nuName) :
    Subtyp κ ((z, s2) :: Γ) (t1.openVar 0 z) (t2.openVar 0 z) := by
  sorry

/-! ## Check.rename / Synth.rename (DEFERRED).

  Bidirectional analogues of `Subtyp.rename`: rename `x → y` at the head of the
  typing context, preserving the bidirectional judgement. The proofs would
  follow the same generalized-Δ pattern as `Subtyp.rename_general` (mutual on
  `Check` / `Synth` derivations, semantic transport for the `.sub` case via
  `Subtyp.rename`). -/

/-- Rename for `Check`, openVar form (matches Check.lam's body shape). -/
theorem Check.rename {κ : KEnv} {Γ : TEnv} {s t : Ty} {e : Exp} (x y : EVar)
    (hx : x ∉ Γ.dom ++ s.fv ++ e.fv ++ t.fv
          ++ Ty.named s ++ Ty.named t
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (hy : y ∉ Γ.dom ++ s.fv ++ e.fv ++ t.fv
          ++ Ty.named s ++ Ty.named t
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (h : Check κ ((x, s) :: Γ) (e.openVar 0 x) (t.openVar 0 x)) :
    Check κ ((y, s) :: Γ) (e.openVar 0 y) (t.openVar 0 y) := by
  sorry

/-- Rename for `Check`, letin form: body type `t` is NOT openVar'd (matches
    Check.letin's body shape, where letin binds the value not the type). -/
theorem Check.rename_letin_body {κ : KEnv} {Γ : TEnv} {s t : Ty} {e : Exp} (x y : EVar)
    (hx : x ∉ Γ.dom ++ s.fv ++ e.fv ++ t.fv
          ++ Ty.named s ++ Ty.named t
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (hy : y ∉ Γ.dom ++ s.fv ++ e.fv ++ t.fv
          ++ Ty.named s ++ Ty.named t
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (h : Check κ ((x, s) :: Γ) (e.openVar 0 x) t) :
    Check κ ((y, s) :: Γ) (e.openVar 0 y) t := by
  sorry

theorem Synth.rename {κ : KEnv} {Γ : TEnv} {s : Ty} {e : Exp} {t : Ty} (x y : EVar)
    (hx : x ∉ Γ.dom ++ s.fv ++ e.fv ++ t.fv
          ++ Ty.named s ++ Ty.named t
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (hy : y ∉ Γ.dom ++ s.fv ++ e.fv ++ t.fv
          ++ Ty.named s ++ Ty.named t
          ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    (h : Synth κ ((x, s) :: Γ) (e.openVar 0 x) (t.openVar 0 x)) :
    Synth κ ((y, s) :: Γ) (e.openVar 0 y) (t.openVar 0 y) := by
  sorry

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
    obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub (t1.openVar 0 (EVar.fresh (s1.fv ++ (s2.fv ++ (t1.fv ++ (t2.fv
                                      ++ (Ty.named s1 ++ (Ty.named s2
                                      ++ (Ty.named t1 ++ (Ty.named t2 ++ [nuName]))))))))))
                                   (t2.openVar 0 (EVar.fresh (s1.fv ++ (s2.fv ++ (t1.fv ++ (t2.fv
                                      ++ (Ty.named s1 ++ (Ty.named s2
                                      ++ (Ty.named t1 ++ (Ty.named t2 ++ [nuName])))))))))) = some c₂ := by grind
    rw [hc₁, hc₂] at hsub ; simp at hsub
    apply Subtyp.arrow (L := Γ.dom ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv ++
                              Ty.named s1 ++ Ty.named s2 ++ Ty.named t1 ++ Ty.named t2 ++
                              TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
    · have h := sub_sound κ Γ s2 s1 c₁ hc₁
      simp at h
      rw [←hsub] at hent
      exact h fun ρ hm => (hent ρ hm).1
    · -- Codomain: use `sub_arrow_codomain_sound` (stated; proof deferred).
      intro z hz
      simp only [List.mem_append, List.mem_singleton, not_or] at hz
      -- Algorithm's NEW fresh name w (now includes Ty.named/[nuName]).
      let L_alg : List EVar := s1.fv ++ (s2.fv ++ (t1.fv ++ (t2.fv ++
                                (Ty.named s1 ++ (Ty.named s2 ++
                                (Ty.named t1 ++ (Ty.named t2 ++ [nuName])))))))
      let w := EVar.fresh L_alg
      have hw_fresh_L : w ∉ L_alg := EVar.fresh_not_mem _
      -- Extract entailment of implyBind from c.
      rw [←hsub] at hent
      have hent_imply : Entail κ Γ (implyBind w s2 c₂ κ) := by
        intro ρ hm
        have h := (hent ρ hm).2
        grind
      have ht1_fv : z ∉ t1.fv := by grind
      have ht2_fv : z ∉ t2.fv := by grind
      have ht1_n : z ∉ Ty.named t1 := by grind
      have ht2_n : z ∉ Ty.named t2 := by grind
      have hs1_fv : z ∉ s1.fv := by grind
      have hs2_fv : z ∉ s2.fv := by grind
      have hs1_n : z ∉ Ty.named s1 := by grind
      have hs2_n : z ∉ Ty.named s2 := by grind
      have hzΓdom : z ∉ Γ.dom := by grind
      have hzΓfv : z ∉ TEnv.tyFv Γ := by grind
      have hzΓn : z ∉ TEnv.tyNamed Γ := by grind
      have hzν : z ≠ nuName := by grind
      -- Algorithm's w now satisfies all the freshness requirements.
      have hwt1 : w ∉ t1.fv := by grind
      have hwt2 : w ∉ t2.fv := by grind
      have hwn1 : w ∉ Ty.named t1 := by grind
      have hwn2 : w ∉ Ty.named t2 := by grind
      have hws2_fv : w ∉ s2.fv := by grind
      have hws2_n : w ∉ Ty.named s2 := by grind
      have hwν : w ≠ nuName := by grind
      apply sub_arrow_codomain_sound (w := w) hc₂ hent_imply
        hwt1 hwt2 hwn1 hwn2 hws2_fv hws2_n hwν
        z hzΓdom hs1_fv hs2_fv ht1_fv ht2_fv ht1_n ht2_n hs1_n hs2_n hzΓfv hzΓn hzν
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
      · exact hcheck.1
      apply check_sound _ _ _ _ _ hc₁
      intro ρ hm
      rw [←hcheck.2] at hent
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
      rw [←hcheck.2] at hent
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
          have hcρ : c κ ρ := hent ρ hΓρ
          rw [← hcheck] at hcρ
          simp only [implyBind] at hcρ
          cases s1 with
          | refine b r =>
            have hsat : Refinement.interp κ r ρ (REnv.get b ρ x₀) := hmρ.1
            have h := hcρ (REnv.get b ρ x₀) hsat
            rw [REnv.update_self] at h
            exact h
          | arrow _ _ => exact hcρ
        -- 2. Cofinite lift via `Check.rename`: transport `hbody₀` (at x₀) to
        --    arbitrary x ∉ L'. The full freshness for `x₀` (Ty.named, tyFv, ...)
        --    isn't guaranteed by check's algorithmic fresh (similar gap to Phase 5);
        -- L' matches Check.rename's hx form (so hxL' directly satisfies hx_fresh).
        let L' : List EVar := Γ.dom ++ s1.fv ++ e.fv ++ Ty.fv t1 ++
                              Ty.named s1 ++ Ty.named t1 ++
                              TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName]
        refine Check.lam L' (fun x hxL' => ?_)
        have hx_fresh : x ∉ Γ.dom ++ s1.fv ++ e.fv ++ Ty.fv t1
                ++ Ty.named s1 ++ Ty.named t1
                ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName] := hxL'
        -- x₀ ∈ L₀ ⊆ (mostly L'); x₀'s freshness against L' follows from EVar.fresh_not_mem.
        have hx₀_fresh : x₀ ∉ Γ.dom ++ s1.fv ++ e.fv ++ Ty.fv t1
                ++ Ty.named s1 ++ Ty.named t1
                ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName] := by
          have hx₀_fresh_L₀ : x₀ ∉ L₀ := EVar.fresh_not_mem _
          -- L₀ is a permutation of the target list (same components, right-assoc parens).
          grind
        exact Check.rename x₀ x hx₀_fresh hx_fresh hbody₀
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
        have hcρ : c κ ρ := hent ρ hΓρ
        rw [← hcheck] at hcρ
        have himply : implyBind x₀ s c₂ κ ρ := by
          have := hcρ.2
          grind
        simp only [implyBind] at himply
        cases s with
        | refine b r =>
          have hsat : Refinement.interp κ r ρ (REnv.get b ρ x₀) := hmρ.1
          have h := himply (REnv.get b ρ x₀) hsat
          rw [REnv.update_self] at h
          exact h
        | arrow _ _ => exact himply
      -- 3. Cofinite lift via `Check.rename_letin_body`.
      -- L' matches Check.rename_letin_body's hx form (so hxL' directly satisfies hx_fresh).
      let L' : List EVar := Γ.dom ++ s.fv ++ e2.fv ++ Ty.fv t ++
                            Ty.named s ++ Ty.named t ++
                            TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName]
      refine Check.letin L' hsy (fun x hxL' => ?_)
      have hx_fresh : x ∉ Γ.dom ++ s.fv ++ e2.fv ++ Ty.fv t
              ++ Ty.named s ++ Ty.named t
              ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName] := hxL'
      -- x₀'s freshness follows from x₀ = EVar.fresh L₀ (L₀ contains all needed components).
      have hx₀_fresh : x₀ ∉ Γ.dom ++ s.fv ++ e2.fv ++ Ty.fv t
              ++ Ty.named s ++ Ty.named t
              ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName] := by
        have hx₀_fresh_L₀ : x₀ ∉ L₀ := EVar.fresh_not_mem _
        grind
      exact Check.rename_letin_body x₀ x hx₀_fresh hx_fresh hbody₀
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
    | .not (.fvar x) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.not (.fvar x)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun ρ hm => (hent ρ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun ρ hm => (hent ρ hm).2)
    | .and (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.and (.fvar x) (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub s' t = some c₂ := by grind
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
    | .lam L hck =>
      rename_i e s₁ s₂
      -- Pick wider L' = L ∪ {nuName} so the chosen x satisfies x ≠ nuName.
      apply Hastype.lam (L := L ++ [nuName]) ht
      intro x hx_in_L'
      simp only [List.mem_append, List.mem_singleton, not_or] at hx_in_L'
      have hxν : x ≠ nuName := hx_in_L'.2
      -- Derive WFBVars facts for the extended context and recursive call.
      have ht_split : Ty.WFBVarCtx [] s₁ ∧ Ty.WFBVarCtx [s₁.optBase] s₂ := by
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at ht; exact ht
      have hs₁_wfb : Ty.WFBVars s₁ := ht_split.1
      have hs₂_open_wfb : Ty.WFBVars (s₂.openVar 0 x) :=
        Ty.WFBVarCtx_openVar_last s₂ [] s₁.optBase x ht_split.2
      have hΓ_ext : TEnv.WFBVars ((x, s₁) :: Γ) := hΓ.cons hs₁_wfb hxν
      have hE_e : Exp.WFBVars e := by simp only [Exp.WFBVars] at hE; exact hE
      have hE_ext : Exp.WFBVars (e.openVar 0 x) := (Exp.WFBVars_openVar e 0 x).mpr hE_e
      exact check_to_hastype hΓ_ext hE_ext hs₂_open_wfb (hck x hx_in_L'.1)
    | .letin L hsy hck =>
      rename_i e₁ e₂ s
      have ⟨hht1, hs_wfb⟩ := synth_to_hastype hΓ hE.1 hsy
      apply Hastype.letin (L := L ++ [nuName]) ht hht1
      intro x hx_in_L'
      simp only [List.mem_append, List.mem_singleton, not_or] at hx_in_L'
      have hxν : x ≠ nuName := hx_in_L'.2
      have hΓ_ext : TEnv.WFBVars ((x, s) :: Γ) := hΓ.cons hs_wfb hxν
      have hE_ext : Exp.WFBVars (e₂.openVar 0 x) :=
        (Exp.WFBVars_openVar e₂ 0 x).mpr hE.2
      exact check_to_hastype hΓ_ext hE_ext ht (hck x hx_in_L'.1)
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
    synth Γ e = some (c, t) → Entail κ Γ (c κ) → Hastype κ Γ e t :=
  fun h hc => (synth_to_hastype hΓ hE (synth_sound κ Γ e c t h hc)).1

theorem check_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    check Γ e t = some c → Entail κ Γ (c κ) → Hastype κ Γ e t :=
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
    exact check_decl_sound κ [] e t c hΓ_nil hE ht hck (Entail.emp h)
