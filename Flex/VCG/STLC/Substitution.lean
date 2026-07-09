import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Model

namespace STLC

/-! ## 1. Term operations -/

/-- Free variables of a term (includes `nuName` if present). -/
def Term.fv : {b : Base} → Term b → List EVar
  | _, .const _ _   => []
  | _, .bvar _ _    => []
  | _, .fvar _ x    => [x]
  | _, .add t₁ t₂   => Term.fv t₁ ++ Term.fv t₂
  | _, .not t       => Term.fv t
  | _, .and t₁ t₂   => Term.fv t₁ ++ Term.fv t₂

/-- Open the `b'`-typed `BVar` at level `k` with a free var `x`.
    A `BVar` of a different base is left untouched. -/
def Term.openBVar (b' : Base) (k : Nat) (x : EVar) :
    {b : Base} → Term b → Term b
  | _, .const b c    => .const b c
  | _, .bvar .int j  =>
      if b' = .int ∧ j = k then .fvar .int x else .bvar .int j
  | _, .bvar .bool j =>
      if b' = .bool ∧ j = k then .fvar .bool x else .bvar .bool j
  | _, .fvar b y     => .fvar b y
  | _, .add t₁ t₂    => .add (Term.openBVar b' k x t₁) (Term.openBVar b' k x t₂)
  | _, .not t        => .not (Term.openBVar b' k x t)
  | _, .and t₁ t₂    => .and (Term.openBVar b' k x t₁) (Term.openBVar b' k x t₂)

/-! ## 2. Formula operations -/

/-- Free variables of a formula. The quantifiers are locally nameless, so they
    bind no name and just pass their body's fv through (the bound `BVar` is not
    an `fvar`). ν is likewise a `BVar`, never an `fvar`, so it never appears. -/
def Formula.fv : Formula → List EVar
  | .tt           => []
  | .ff           => []
  | .eq _ t₁ t₂   => t₁.fv ++ t₂.fv
  | .leqI t₁ t₂   => t₁.fv ++ t₂.fv
  | .and φ₁ φ₂    => Formula.fv φ₁ ++ Formula.fv φ₂
  | .or φ₁ φ₂     => Formula.fv φ₁ ++ Formula.fv φ₂
  | .not φ        => Formula.fv φ
  | .imp φ₁ φ₂    => Formula.fv φ₁ ++ Formula.fv φ₂
  | .ex _  φ      => Formula.fv φ
  | .all _ φ      => Formula.fv φ

/-- Open the `b'`-typed `BVar` at level `k` with a free var `x` throughout `φ`.
    Crossing a quantifier binds a fresh innermost `BVar`, so the level bumps. -/
def Formula.openBVar (b' : Base) (k : Nat) (x : EVar) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eq b t₁ t₂   => .eq b (t₁.openBVar b' k x) (t₂.openBVar b' k x)
  | .leqI t₁ t₂   => .leqI (t₁.openBVar b' k x) (t₂.openBVar b' k x)
  | .and φ₁ φ₂    => .and (φ₁.openBVar b' k x) (φ₂.openBVar b' k x)
  | .or φ₁ φ₂     => .or (φ₁.openBVar b' k x) (φ₂.openBVar b' k x)
  | .not φ        => .not (φ.openBVar b' k x)
  | .imp φ₁ φ₂    => .imp (φ₁.openBVar b' k x) (φ₂.openBVar b' k x)
  | .ex b φ       => .ex b (φ.openBVar b' (k+1) x)
  | .all b φ      => .all b (φ.openBVar b' (k+1) x)

/-! ## 3. Refinement operations -/

/-- Free variables of a refinement. ν is a `BVar` (level 0), never an `fvar`,
    so the formula's fv already excludes it — no filtering needed. -/
def Refinement.fv (r : Refinement) : List EVar :=
  match r with
  | .fmla φ      => φ.fv
  | .kapp _ args => args.flatMap (fun a => Term.fv a.2)

def Refinement.openBVar (b' : Base) (k : Nat) (x : EVar)
    (r : Refinement) : Refinement :=
  match r with
  | .fmla φ       => .fmla (φ.openBVar b' k x)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, Term.openBVar b' k x a.2⟩))

/-- Refinement type for an integer constant: `{ν : Int | ν = n}` (ν = `BVar 0`). -/
@[simp] def prim (n : Int) : Ty :=
  .refine .int (.fmla (.eq .int (.bvar .int 0) (.const .int n)))

/-- Refinement type for a boolean constant: `{ν : Bool | ν = b}` (ν = `BVar 0`). -/
@[simp] def primBool (b : Bool) : Ty :=
  .refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.const .bool b)))

/-- `self x t` is the *singleton* refinement `{ν | ν = x}` against the stored
    value of `x` (selfification), with ν = `BVar 0`. The variable's own
    refinement is recovered from the typing context, so it is not re-conjoined
    here — keeping the synthesized type kvar-free. For function types, returns
    `t` unchanged. -/
@[simp] def self : EVar → Ty → Ty
  | x, .refine .int  _ => .refine .int  (.fmla
      (.eq .int (.bvar .int  0) (.fvar .int  x)))
  | x, .refine .bool _ => .refine .bool (.fmla
      (.eq .bool (.bvar .bool 0) (.fvar .bool x)))
  | _, .arrow t1 t2    => .arrow t1 t2

/-! ## 4. Ty operations (locally nameless)

  `Ty.openVar k b x t` substitutes the `b`-typed `BVar` at level `k` with
  `fvar b x` throughout refinements in `t`. Crossing a `Ty.arrow` binder
  bumps the level. `arrow`'s domain is at the same level as the parent
  (it's not under the arrow's binder); the codomain is at `k+1`.
-/

def Ty.fv : Ty → List EVar
  | .refine _ r => r.fv
  | .arrow s t  => Ty.fv s ++ Ty.fv t

/-- Open a `Ty`'s outermost binder at level `k` with free name `x`. Replaces
    `Term.bvar b (k+1)` for BOTH bases (int and bool) in every refinement
    formula — the `+1` because ν occupies formula-level 0, so arrow binders
    live one level out. In a well-formed type at most one base's BVars appear at
    each level, so one of the two openBVar calls is always a no-op. -/
def Ty.openVar (k : Nat) (x : EVar) : Ty → Ty
  | .refine b r => .refine b ((r.openBVar .int (k+1) x).openBVar .bool (k+1) x)
  | .arrow s t  => .arrow (s.openVar k x) (t.openVar (k+1) x)

@[simp]
theorem Ty.skel_openVar (k : Nat) (x : EVar) (t : Ty) :
    (t.openVar k x).skel = t.skel := by
  induction t generalizing k with
  | refine _ _ => rfl
  | arrow s t ihs iht => simp [Ty.openVar, Ty.skel, ihs, iht]

/-! ### Well-formedness: BVar base consistency (WFBVarCtx)

  In coq-SystemRF, `WFtype` ensures that bound variables in predicate formulas
  match the base of the enclosing binder's domain type.  In our system, this is
  `Ty.WFBVarCtx ctx t`: for each level `k`, all `BVar b k` in `t`'s refinement
  formulas have `ctx[k]? = some (some b)` (the k-th outer arrow binder's domain base).

  This predicate is required by `TyDenote.push_iff` to make `openBVar` of
  the "other" base a provable no-op when the formula is well-formed. -/

/-- `Term.hasBVar b k t`: t contains at least one `Term.bvar b k`. -/
def Term.hasBVar (b : Base) (k : Nat) : {b' : Base} → Term b' → Prop
  | _, .const _ _  => False
  | _, .bvar b' j  => b = b' ∧ k = j
  | _, .fvar _ _   => False
  | _, .add t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | _, .not t      => Term.hasBVar b k t
  | _, .and t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂

/-- `Formula.hasBVar b k φ`: φ contains at least one `Term.bvar b k`. -/
def Formula.hasBVar (b : Base) (k : Nat) : Formula → Prop
  | .tt | .ff => False
  | .eq _ t₁ t₂ | .leqI t₁ t₂ =>
      Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | .and φ₁ φ₂ | .or φ₁ φ₂ | .imp φ₁ φ₂ =>
      Formula.hasBVar b k φ₁ ∨ Formula.hasBVar b k φ₂
  | .not φ => Formula.hasBVar b k φ
  | .ex _ φ | .all _ φ =>
      -- each quantifier binds the innermost BVar, so outer levels shift up
      Formula.hasBVar b (k+1) φ

/-- `Refinement.hasBVar b k r`: r mentions `Term.bvar b k` — in its formula, or
    in the arguments of a κ-application. -/
def Refinement.hasBVar (b : Base) (k : Nat) (r : Refinement) : Prop :=
  match r with
  | .fmla φ      => Formula.hasBVar b k φ
  | .kapp _ args => ∃ a ∈ args, Term.hasBVar b k a.2

/-- Extract the base of a refinement type; None for arrow types. -/
def Ty.optBase : Ty → Option Base
  | .refine b _ => some b
  | .arrow _ _  => none

/-- `Ty.WFBVarCtx ctx t`: at nesting depth k, all `BVar b k` in `t`'s
    refinement formulas satisfy `(some bᵣ :: ctx)[k]? = some (some b)`, where
    `bᵣ` is the refinement's own base. Level 0 is ν (always base `bᵣ`); level
    `k+1` is the k-th outer arrow binder (`ctx[k]`). -/
def Ty.WFBVarCtx : List (Option Base) → Ty → Prop
  | ctx, .refine br r =>
      ∀ (b : Base) (k : Nat), Refinement.hasBVar b k r → (some br :: ctx)[k]? = some (some b)
  | ctx, .arrow s t  =>
      Ty.WFBVarCtx ctx s ∧ Ty.WFBVarCtx (s.optBase :: ctx) t

/-- Shorthand: `t` is well-formed with no outer binders. -/
def Ty.WFBVars (t : Ty) : Prop := Ty.WFBVarCtx [] t

/-- A typing context is WFBVars iff every binding's type is `Ty.WFBVars`. (With
    ν locally nameless there is no reserved name to keep out of the domain.) -/
def TEnv.WFBVars (Γ : TEnv) : Prop :=
  ∀ x t, (x, t) ∈ Γ → Ty.WFBVars t

/-- All type annotations syntactically present in `e` are `Ty.WFBVars`.
    Used as a precondition on soundness theorems so the `.ann` case has the
    WFBVars evidence to construct the corresponding `Hastype` node. -/
def Exp.WFBVars : Exp → Prop
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ => True
  | .lam e        => Exp.WFBVars e
  | .letin e₁ e₂  => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .app e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .ann e t      => Ty.WFBVars t ∧ Exp.WFBVars e
  | .and e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .not e        => Exp.WFBVars e
  | .leq e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .ite e₀ e₁ e₂ => Exp.WFBVars e₀ ∧ Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .add e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂

theorem TEnv.WFBVars.empty : TEnv.WFBVars [] := by intros x t h ; trivial

/-- Cons preserves `TEnv.WFBVars` given the new binding has WFBVars type. -/
theorem TEnv.WFBVars.cons {Γ : TEnv} {x : EVar} {t : Ty}
    (hΓ : TEnv.WFBVars Γ) (ht : Ty.WFBVars t) :
    TEnv.WFBVars ((x, t) :: Γ) := by
  intro y s h
  simp only [List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨_, hst⟩ | h
  · exact hst ▸ ht
  · exact hΓ y s h

/-- Lookup in a WFBVars context yields a WFBVars type. -/
theorem TEnv.WFBVars.lookup {Γ : TEnv} (hΓ : TEnv.WFBVars Γ) {x : EVar} {t : Ty}
    (hlk : Γ.lookup x = some t) : Ty.WFBVars t := by
  induction Γ with
  | nil => simp [List.lookup] at hlk
  | cons hd tl ih =>
    obtain ⟨y, s⟩ := hd
    simp only [List.lookup] at hlk
    by_cases hxy : x = y
    · have heq : (x == y) = true := by simp [hxy]
      rw [heq] at hlk
      have hst : s = t := Option.some.inj hlk
      subst hst
      exact hΓ y s (by simp)
    · have hne : (x == y) = false := by simp [hxy]
      rw [hne] at hlk
      have hΓ_tl : TEnv.WFBVars tl := fun z r h => hΓ z r (by simp [List.mem_cons, h])
      exact ih hΓ_tl hlk

/-- If t has no `BVar b k`, then `Term.openBVar b k x` is the identity. -/
theorem Term.openBVar_noop (b : Base) (k : Nat) (x : EVar) :
    ∀ {b' : Base} (t : Term b'), ¬Term.hasBVar b k t → Term.openBVar b k x t = t := by
  intro b' t h
  induction t with
  | const _ _ => simp [Term.openBVar]
  | bvar b'' j =>
    simp [Term.hasBVar] at h
    cases b'' <;> cases b <;> simp_all [Term.openBVar, Ne.symm]
  | fvar _ _ => simp [Term.openBVar]
  | add t₁ t₂ ih1 ih2 =>
    simp [Term.hasBVar] at h
    simp [Term.openBVar, ih1 h.1, ih2 h.2]
  | not t ih =>
    simp [Term.hasBVar] at h
    simp [Term.openBVar, ih h]
  | and t₁ t₂ ih1 ih2 =>
    simp [Term.hasBVar] at h
    simp [Term.openBVar, ih1 h.1, ih2 h.2]

/-- If φ has no `BVar b k`, then `openBVar b k x` is the identity. -/
theorem Formula.openBVar_noop (φ : Formula) (b : Base) (k : Nat) (x : EVar)
    (h : ¬Formula.hasBVar b k φ) : φ.openBVar b k x = φ := by
  induction φ generalizing k with
  | tt | ff => simp [Formula.openBVar]
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar] at h
    simp [Formula.openBVar, Term.openBVar_noop b k x _ h.1, Term.openBVar_noop b k x _ h.2]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar] at h
    simp [Formula.openBVar, ih1 k h.1, ih2 k h.2]
  | not φ ih =>
    simp [Formula.hasBVar] at h
    simp [Formula.openBVar, ih k h]
  | ex _ φ ih  | all _ φ ih =>
    simp only [Formula.hasBVar] at h
    simp [Formula.openBVar, ih (k+1) h]

/-- Opening a term at (b, k) eliminates all BVar b k occurrences. -/
private theorem Term.not_hasBVar_openBVar_same (b : Base) (k : Nat) (x : EVar) :
    ∀ {b' : Base} (t : Term b'), ¬Term.hasBVar b k (Term.openBVar b k x t) := by
  intro b' t
  induction t with
  | const _ _ => simp [Term.openBVar, Term.hasBVar]
  | bvar b'' j =>
    cases b'' <;> cases b <;> simp_all [Term.openBVar, Term.hasBVar]
      <;> by_cases j = k <;> grind [Term.openBVar, Term.hasBVar]
  | fvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | add t₁ t₂ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]
  | not t ih  => simp [Term.openBVar, Term.hasBVar, ih]
  | and t₁ t₂ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]

/-- Opening at (b', j) preserves hasBVar b k when (b, k) ≠ (b', j). -/
private theorem Term.hasBVar_openBVar_other {b'' : Base} (t : Term b'')
    (b b' : Base) (k j : Nat) (x : EVar) (hne : b ≠ b' ∨ k ≠ j) :
    Term.hasBVar b k (Term.openBVar b' j x t) ↔ Term.hasBVar b k t := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.hasBVar]
  | bvar b'' i =>
    cases b'' <;> cases b <;> cases b' <;> simp_all [Term.openBVar, Term.hasBVar] <;> grind [hasBVar]
  | fvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | add _ _ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]
  | not _ ih  => simp [Term.openBVar, Term.hasBVar, ih]
  | and _ _ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]

/-- Opening φ at (b, k) eliminates all hasBVar b k. -/
theorem Formula.not_hasBVar_openBVar_same (φ : Formula) (b : Base) (k : Nat) (x : EVar) :
    ¬Formula.hasBVar b k (φ.openBVar b k x) := by
  induction φ generalizing k with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar, Formula.openBVar, Term.not_hasBVar_openBVar_same]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar, Formula.openBVar, ih1, ih2]
  | not φ ih | ex _ φ ih | all _ φ ih =>
    simp [Formula.hasBVar, Formula.openBVar, ih]

/-- Opening φ at (b', j) with (b, k) ≠ (b', j) preserves hasBVar b k. -/
theorem Formula.hasBVar_openBVar_other (φ : Formula) (b b' : Base) (k j : Nat) (x : EVar)
    (hne : b ≠ b' ∨ k ≠ j) :
    Formula.hasBVar b k (φ.openBVar b' j x) ↔ Formula.hasBVar b k φ := by
  induction φ generalizing k j with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar, Formula.openBVar,
          Term.hasBVar_openBVar_other _ b b' k j x hne]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar, Formula.openBVar, ih1 k j hne, ih2 k j hne]
  | not φ ih => simp [Formula.hasBVar, Formula.openBVar, ih k j hne]
  | ex _ φ ih | all _ φ ih =>
    simp only [Formula.openBVar, Formula.hasBVar]
    exact ih (k+1) (j+1) (hne.imp_right (fun h => by omega))

/-! Refinement-level analogues of the `Formula.*` openBVar BVar lemmas: case-split
    the enum and dispatch κ-application arguments via the `Term.*` lemmas. -/

theorem Refinement.not_hasBVar_openBVar_same (r : Refinement)
    (b : Base) (k : Nat) (x : EVar) : ¬Refinement.hasBVar b k (r.openBVar b k x) := by
  cases r with
  | fmla φ => exact Formula.not_hasBVar_openBVar_same φ b k x
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar]
    rintro ⟨a, hmem, hbv⟩
    simp only [List.mem_map] at hmem
    obtain ⟨a', _, rfl⟩ := hmem
    exact Term.not_hasBVar_openBVar_same b k x a'.2 hbv

theorem Refinement.hasBVar_openBVar_other (r : Refinement)
    (b b' : Base) (k j : Nat) (x : EVar) (hne : b ≠ b' ∨ k ≠ j) :
    Refinement.hasBVar b k (r.openBVar b' j x) ↔ Refinement.hasBVar b k r := by
  cases r with
  | fmla φ => exact Formula.hasBVar_openBVar_other φ b b' k j x hne
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar]
    constructor
    · rintro ⟨a, hmem, hbv⟩
      simp only [List.mem_map] at hmem
      obtain ⟨a', hmem', rfl⟩ := hmem
      exact ⟨a', hmem', (Term.hasBVar_openBVar_other a'.2 b b' k j x hne).mp hbv⟩
    · rintro ⟨a, hmem, hbv⟩
      exact ⟨⟨a.1, Term.openBVar b' j x a.2⟩,
             by simp only [List.mem_map]; exact ⟨a, hmem, rfl⟩,
             (Term.hasBVar_openBVar_other a.2 b b' k j x hne).mpr hbv⟩

/-- Refinement-level `openBVar_noop`: opening at a base/level with no occurrence
    is the identity. -/
theorem Refinement.openBVar_noop (r : Refinement) (b : Base) (k : Nat)
    (x : EVar) (h : ¬Refinement.hasBVar b k r) : Refinement.openBVar b k x r = r := by
  cases r with
  | fmla φ =>
    simp only [Refinement.openBVar]
    rw [Formula.openBVar_noop φ b k x (by simpa [Refinement.hasBVar] using h)]
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar] at h ⊢
    congr 1
    have hmap : ∀ a ∈ args,
        (fun a => (⟨a.1, Term.openBVar b k x a.2⟩ : Σ b : Base, Term b)) a = id a := by
      intro a ha
      simp only [id]; congr 1
      exact Term.openBVar_noop b k x a.2 (fun hbv => h ⟨a, ha, hbv⟩)
    simp [List.map_congr_left hmap]

/-- `optBase` is unchanged by `openVar` (shape refine/arrow is preserved). -/
theorem Ty.optBase_openVar (t : Ty) (k : Nat) (y : EVar) :
    (t.openVar k y).optBase = t.optBase := by
  cases t <;> simp [Ty.openVar, Ty.optBase]

/-- Opening at level `ctx.length` (the last binder position) consumes the last
    context entry. For the `app` case use ctx = [], opt = s.optBase:
    `WFBVarCtx [s.optBase] t → WFBVarCtx [] (t.openVar 0 y)`. -/
theorem Ty.WFBVarCtx_openVar_last (t : Ty) (ctx : List (Option Base)) (opt : Option Base)
    (y : EVar) (hWF : Ty.WFBVarCtx (ctx ++ [opt]) t) :
    Ty.WFBVarCtx ctx (t.openVar ctx.length y) := by
  induction t generalizing ctx with
  | refine b r =>
    -- ν occupies formula-level 0 (base `b`), so the arrow binder opened by
    -- `openVar ctx.length` lives at formula-level `ctx.length + 1`, and the
    -- WFBVarCtx index list is `some b :: …`.
    simp only [Ty.openVar, Ty.WFBVarCtx] at hWF ⊢
    intro b' k hbv
    by_cases hklen : k = ctx.length + 1
    · -- k = ctx.length+1: this is the opened level — no BVar survives
      subst hklen
      cases b' with
      | int =>
        have hno : ¬Refinement.hasBVar .int (ctx.length + 1)
            ((r.openBVar .int (ctx.length + 1) y).openBVar .bool (ctx.length + 1) y) := by
          rw [Refinement.hasBVar_openBVar_other _ .int .bool (ctx.length + 1) (ctx.length + 1) y
                (Or.inl (by decide))]
          exact Refinement.not_hasBVar_openBVar_same _ .int (ctx.length + 1) y
        exact absurd hbv hno
      | bool =>
        exact absurd hbv (Refinement.not_hasBVar_openBVar_same _ .bool (ctx.length + 1) y)
    · -- k ≠ ctx.length+1: BVar k survived both openings → it was in original r.
      have hbv' : Refinement.hasBVar b' k r := by
        rw [Refinement.hasBVar_openBVar_other _ _ _ _ _ _ (Or.inr hklen),
            Refinement.hasBVar_openBVar_other _ _ _ _ _ _ (Or.inr hklen)] at hbv
        exact hbv
      have hWF' := hWF b' k hbv'
      -- strip the `some b ::` prepend; level 0 (ν) is shared, level k'+1 indexes ctx
      cases k with
      | zero => simpa using hWF'
      | succ k' =>
        have hk' : k' ≠ ctx.length := fun h => hklen (by omega)
        simp only [List.getElem?_cons_succ, List.getElem?_append] at hWF' ⊢
        by_cases hklt : k' < ctx.length
        · simp [hklt] at hWF' ⊢; exact hWF'
        · have hkge : ctx.length ≤ k' := Nat.le_of_not_lt hklt
          simp [Nat.not_lt.mpr hkge] at hWF'
          grind
  | arrow s t ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.openVar]
    refine ⟨ihs ctx hWF.1, ?_⟩
    -- Codomain uses IH with ctx' = s.optBase :: ctx
    have ih := iht (s.optBase :: ctx) (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih

/-- For k > ctx.length, both (ctx ++ [opt])[k]? and (ctx ++ [none])[k]? are none. -/
private theorem List.getElem?_append_singleton_gt (opt : α) (ctx : List α) (k : Nat)
    (hgt : ctx.length < k) : (ctx ++ [opt])[k]? = none := by
  rw [List.getElem?_eq_none_iff]
  simp; omega

/-- For k ≠ ctx.length, replacing the element at ctx.length doesn't affect index k. -/
private theorem optBase_list_getElem?_update_middle (ctx : List (Option Base)) (a b : Option Base)
    (rest : List (Option Base)) (k : Nat) (hk : k ≠ ctx.length) :
    (ctx ++ [a] ++ rest)[k]? = (ctx ++ [b] ++ rest)[k]? := by
  induction ctx generalizing k with
  | nil =>
    simp only [List.nil_append, List.length_nil] at hk ⊢
    rcases k with _ | k
    · exact absurd rfl hk
    · simp [List.getElem?_cons_succ]
  | cons hd tl ih =>
    simp only [List.cons_append, List.length_cons] at hk ⊢
    rcases k with _ | k
    · rfl
    · simp only [List.getElem?_cons_succ]
      exact ih _ (by omega)

/-- The element at ctx.length in ctx ++ [a] ++ rest is some a. -/
private theorem optBase_list_getElem?_middle (ctx : List (Option Base)) (a : Option Base)
    (rest : List (Option Base)) :
    (ctx ++ [a] ++ rest)[ctx.length]? = some a := by
  induction ctx with
  | nil => simp
  | cons hd tl ih => simp

/-! ## 5. Exp operations (locally nameless)

  (Val is declared in `Syntax.lean`; its operations follow below in §5b.) -/

/-- Replace `bvar k` with `fvar x` (used when entering a binder). -/
def Exp.openVar (k : Nat) (x : EVar) : Exp → Exp
  | .bvar j        => if j = k then .fvar x else .bvar j
  | .fvar y        => .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (body.openVar (k+1) x)
  | .letin e₁ e₂   => .letin (e₁.openVar k x) (e₂.openVar (k+1) x)
  | .app e₁ e₂     => .app (e₁.openVar k x) (e₂.openVar k x)
  | .ann e t       => .ann (e.openVar k x) t
  | .and e₁ e₂     => .and (e₁.openVar k x) (e₂.openVar k x)
  | .not e         => .not (e.openVar k x)
  | .leq e₁ e₂     => .leq (e₁.openVar k x) (e₂.openVar k x)
  | .ite e₀ e₁ e₂  => .ite (e₀.openVar k x) (e₁.openVar k x) (e₂.openVar k x)
  | .add e₁ e₂     => .add (e₁.openVar k x) (e₂.openVar k x)

/-- Structural skeleton size: counts constructor depth, ignoring leaf details
    (so `Exp.skel` is preserved under `openVar` / `subst`). Used as a
    termination measure for algorithmic functions in `VCGen.lean`. -/
@[simp]
def Exp.skel : Exp → Nat
  | .bvar _        => 0
  | .fvar _        => 0
  | .iconst _      => 0
  | .bconst _      => 0
  | .lam body      => 1 + body.skel
  | .letin e₁ e₂   => 1 + e₁.skel + e₂.skel
  | .app e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .ann e _       => 1 + e.skel
  | .and e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .not e         => 1 + e.skel
  | .leq e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .ite e₀ e₁ e₂  => 1 + e₀.skel + e₁.skel + e₂.skel
  | .add e₁ e₂     => 1 + e₁.skel + e₂.skel

@[simp]
theorem Exp.skel_openVar (k : Nat) (x : EVar) (e : Exp) :
    (e.openVar k x).skel = e.skel := by
  induction e generalizing k with
  | bvar j        => simp [Exp.openVar]; split <;> rfl
  | fvar _        => rfl
  | iconst _      => rfl
  | bconst _      => rfl
  | lam _ ih      => simp [Exp.openVar, Exp.skel, ih]
  | letin _ _ ih₁ ih₂  => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | app _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | ann _ _ ih         => simp [Exp.openVar, Exp.skel, ih]
  | and _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | not _ ih           => simp [Exp.openVar, Exp.skel, ih]
  | leq _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | ite _ _ _ ih₀ ih₁ ih₂ => simp [Exp.openVar, Exp.skel, ih₀, ih₁, ih₂]
  | add _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]

/-! ## 7. TEnv free variables -/

/-- Flat union of all type free-variables in Γ (no scoping filter). Used for
    freshness conditions: x ∉ TEnv.tyFv Γ ↔ ∀ (y,t) ∈ Γ, x ∉ t.fv. -/
def TEnv.tyFv : TEnv → List EVar
  | []          => []
  | (_, t) :: Γ => t.fv ++ TEnv.tyFv Γ


/-! ## 8. Closing substitution (for big-step / fundamental lemma) -/

/-- Closing substitution driven by the runtime environment `γ`. Since `γ` is a
    *total* function `EVar → Val`, this is a structural *simultaneous* value
    substitution: every free name `x` is replaced by `(γ.map x).toExp`. No domain
    is needed — on a well-typed term every free name is bound in the model, and
    the `iconst 0` default never occurs at a name that is actually read.-/
def Exp.substEnv (γ : REnv) : Exp → Exp
  | .bvar j       => .bvar j
  | .fvar x       => (γ.map x).toExp
  | .iconst n     => .iconst n
  | .bconst b     => .bconst b
  | .lam body     => .lam (Exp.substEnv γ body)
  | .letin e₁ e₂  => .letin (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .app e₁ e₂    => .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .ann e t      => .ann (Exp.substEnv γ e) t
  | .add e₁ e₂    => .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .leq e₁ e₂    => .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .not e        => .not (Exp.substEnv γ e)
  | .and e₁ e₂    => .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .ite e₀ e₁ e₂ => .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)

/-! ## 9. Freshness helper

  `EVar.fresh L` returns a name not in `L`, by producing a string longer than
  any element of `L`. The freshness proof lives in Stage 2b. -/

def EVar.maxLen : List EVar → Nat
  | []      => 0
  | x :: xs => Nat.max x.length (EVar.maxLen xs)

def EVar.fresh (L : List EVar) : EVar :=
  String.ofList (List.replicate (EVar.maxLen L + 1) 'x')

/-! ## 10. REnv helpers -/

@[simp] theorem REnv.get_update_same (b : Base) (γ : REnv) (x : EVar) (v : b.interp) :
    REnv.get b (γ.update b x v) x = v := by
  cases b <;> simp [REnv.get]

/-! ## 11. EVar.fresh proof -/

private theorem EVar.maxLen_ge {L : List EVar} {s : EVar} (h : s ∈ L) :
    s.length ≤ EVar.maxLen L := by
  induction L with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [EVar.maxLen]; exact Nat.le_max_left _ _
    · simp [EVar.maxLen]
      exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

private theorem EVar.fresh_length (L : List EVar) :
    (EVar.fresh L).length = EVar.maxLen L + 1 := by
  show (String.ofList (List.replicate (EVar.maxLen L + 1) 'x')).length
       = EVar.maxLen L + 1
  rw [String.length_ofList, List.length_replicate]

theorem EVar.fresh_not_mem (L : List EVar) : EVar.fresh L ∉ L := by
  intro h
  have h₁ : (EVar.fresh L).length = EVar.maxLen L + 1 := EVar.fresh_length L
  have h₂ : (EVar.fresh L).length ≤ EVar.maxLen L := EVar.maxLen_ge h
  rw [h₁] at h₂
  omega

/-- A fresh name is `≠` any member of the list it was drawn from — decided by
    *length* (`EVar.maxLen`), not by comparing the `x`-strings character by
    character (which is prohibitively deep for nested contexts). Stated as
    `beq = false` so it fires as a `simp` rewrite on `if · == · …`. -/
@[simp] theorem EVar.fresh_beq_mem_left (L : List EVar) (x : EVar) (h : x ∈ L) :
    (EVar.fresh L == x) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq; subst heq; exact EVar.fresh_not_mem L h

@[simp] theorem EVar.fresh_beq_mem_right (L : List EVar) (x : EVar) (h : x ∈ L) :
    (x == EVar.fresh L) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq; subst heq; exact EVar.fresh_not_mem L h

/-! ## 15. `Exp.substEnv` push-through lemmas

  Under the structural definition each constructor case is *definitional*
  (`rfl`); the lemmas are kept (as `@[simp]`) so existing call sites and the
  `simp` set continue to fire by name. -/

@[simp]
theorem Exp.substEnv_fvar (γ : REnv) (x : EVar) :
    Exp.substEnv γ (.fvar x) = (γ.map x).toExp := rfl

@[simp]
theorem Exp.substEnv_iconst (γ : REnv) (n : Int) :
    Exp.substEnv γ (.iconst n) = .iconst n := rfl

@[simp]
theorem Exp.substEnv_bconst (γ : REnv) (b : Bool) :
    Exp.substEnv γ (.bconst b) = .bconst b := rfl

@[simp]
theorem Exp.substEnv_lam (γ : REnv) (body : Exp) :
    Exp.substEnv γ (.lam body) = .lam (Exp.substEnv γ body) := rfl

@[simp]
theorem Exp.substEnv_letin (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.letin e₁ e₂) = .letin (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_app (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.app e₁ e₂) = .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_ann (γ : REnv) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.ann e t) = .ann (Exp.substEnv γ e) t := rfl

@[simp]
theorem Exp.substEnv_add (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.add e₁ e₂) = .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_leq (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.leq e₁ e₂) = .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_not (γ : REnv) (e : Exp) :
    Exp.substEnv γ (.not e) = .not (Exp.substEnv γ e) := rfl

@[simp]
theorem Exp.substEnv_and (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.and e₁ e₂) = .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_ite (γ : REnv) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv γ (.ite e₀ e₁ e₂) = .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

/-- A closed expression is fixed under the closing substitution. -/
theorem Exp.substEnv_closed (γ : REnv) (e : Exp) (he : e.fv = []) :
    Exp.substEnv γ e = e := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar y => simp [Exp.fv] at he
  | lam body ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | ann e t ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | not e ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.append_eq_nil_iff] at he
    simp only [Exp.substEnv, ih₁ he.1, ih₂ he.2]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.append_eq_nil_iff] at he
    simp only [Exp.substEnv, ih₀ he.1.1, ih₁ he.1.2, ih₂ he.2]

theorem Val.toExp_closed_of_closed {v : Val} (h : Val.closed v) : v.toExp.fv = [] := by
  cases v with
  | iconst _   => simp [Val.toExp, Exp.fv]
  | bconst _   => simp [Val.toExp, Exp.fv]
  | clos body  =>
    simp [Val.closed, Val.fv] at h
    simp [Val.toExp, Exp.fv, h]

theorem Val.toExp_lc_at_zero {v : Val} (h : Val.lc v) : Exp.lc_at 0 v.toExp := by
  cases v with
  | iconst _  => simp [Val.toExp, Exp.lc_at]
  | bconst _  => simp [Val.toExp, Exp.lc_at]
  | clos body =>
    simp only [Val.lc] at h
    simp only [Val.toExp, Exp.lc_at]
    exact h

/-- If every free name of `e` is mapped to a closed value by `γ`, then the
    closing substitution produces a closed expression. -/
theorem Exp.substEnv_fv_nil (γ : REnv) (e : Exp)
    (hcl : ∀ z ∈ e.fv, Val.closed (γ.map z)) :
    (Exp.substEnv γ e).fv = [] := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar x => exact Val.toExp_closed_of_closed (hcl x (by simp [Exp.fv]))
  | lam body ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | ann e t ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | not e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨ih₁ fun z hz => hcl z (by simp [Exp.fv, hz]),
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨⟨ih₀ fun z hz => hcl z (by simp [Exp.fv, hz]),
            ih₁ fun z hz => hcl z (by simp [Exp.fv, hz])⟩,
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩

/-! ## 17b. openVar of lc_at is identity -/

/-- Converse of openVar_of_lc_at: if opening e at depth k with any name gives lc_at k,
    then e itself is lc_at (k+1). This is the standard LN "body is lc" lemma. -/
theorem Exp.lc_at_of_openVar (e : Exp) (k : Nat) (x : EVar)
    (h : (e.openVar k x).lc_at k) : e.lc_at (k + 1) := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar] at h
    simp only [Exp.lc_at]
    by_cases hjk : j = k
    · subst hjk; omega
    · simp only [hjk, ↓reduceIte, Exp.lc_at] at h; omega
  | fvar _ => trivial
  | iconst _ => trivial
  | bconst _ => trivial
  | lam body ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih (k + 1) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | ann e t ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | not e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2⟩
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩

/-- openExp with any u is identity when e has lc_at k (no BVar k inside). -/
theorem Exp.openExp_of_lc_at (e : Exp) (k : Nat) (u : Exp) (h : Exp.lc_at k e) :
    Exp.openExp k u e = e := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openExp, if_neg (Nat.ne_of_lt h)]
  | fvar _ => rfl
  | iconst _ => rfl
  | bconst _ => rfl
  | lam body ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih (k+1) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₁ k h.1, ih₂ (k+1) h.2]
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | ann e t ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | not e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2

/-- lc_at is monotone: lc_at j implies lc_at k for k ≥ j. -/
theorem Exp.lc_at_mono (e : Exp) {j k : Nat} (hjk : j ≤ k) (h : Exp.lc_at j e) :
    Exp.lc_at k e := by
  induction e generalizing j k with
  | bvar i => exact Nat.lt_of_lt_of_le h hjk
  | fvar _ => trivial
  | iconst _ => trivial
  | bconst _ => trivial
  | lam body ih =>
    simp only [Exp.lc_at] at *
    exact ih (Nat.succ_le_succ hjk) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ (Nat.succ_le_succ hjk) h.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | ann e t ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | not e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₀ hjk h.1, ih₁ hjk h.2.1, ih₂ hjk h.2.2⟩
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩

/-! ## 17b. subst/substEnv preserve lc_at -/

theorem Exp.substEnv_lc_at (γ : REnv) (e : Exp) (k : Nat)
    (hγ : ∀ z ∈ e.fv, Val.lc (γ.map z)) (hlc_e : e.lc_at k) :
    (e.substEnv γ).lc_at k := by
  induction e generalizing k with
  | bvar j => simpa [Exp.substEnv] using hlc_e
  | iconst _ | bconst _ => trivial
  | fvar x =>
    exact Exp.lc_at_mono _ (Nat.zero_le k) (Val.toExp_lc_at_zero (hγ x (by simp [Exp.fv])))
  | lam body ih =>
    exact ih (k+1) (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | ann e t ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | not e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | letin e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ (k+1) (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    obtain ⟨h₀, h₁, h₂⟩ := hlc_e
    exact ⟨ih₀ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₀,
           ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩


/-! ## 19. substEnv-openVal: key lemma for lam/letin cases -/

theorem REnv.write_self (γ : REnv) (x : EVar) (v : Val) : (γ.write x v).map x = v := by
  simp

theorem REnv.write_other (γ : REnv) (x : EVar) (v : Val) {y : EVar} (h : x ≠ y) :
    (γ.write x v).map y = γ.map y := by
  have hxy : (x == y) = false := by simp [h]
  simp [hxy]

/-- Writing a cell's current value back is the identity (no `HasBase` needed,
    since `write` is lossless). Drives the simplified `app` case of the
    fundamental lemma. -/
theorem REnv.write_idem (γ : REnv) (x : EVar) : γ.write x (γ.map x) = γ := by
  apply REnv.ext
  · funext y
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  · rfl

/-- The closing substitution depends only on `γ` over the free names of `e`. -/
theorem Exp.substEnv_congr (e : Exp) (γ₁ γ₂ : REnv)
    (h : ∀ z ∈ e.fv, γ₁.map z = γ₂.map z) :
    Exp.substEnv γ₁ e = Exp.substEnv γ₂ e := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar x => simp only [Exp.substEnv, h x (by simp [Exp.fv])]
  | lam e ih | ann e _ ih | not e ih =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simpa [Exp.fv] using hz)]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₀ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]

/-- Extending `γ` at a name `y` not free in `e` does not change `substEnv`. The
    single-env analogue of the old `substEnv_cons_fresh`. -/
theorem Exp.substEnv_write_fresh (e : Exp) (γ : REnv) (y : EVar) (v : Val)
    (h : y ∉ e.fv) :
    Exp.substEnv (γ.write y v) e = Exp.substEnv γ e := by
  apply Exp.substEnv_congr
  intro z hz
  exact REnv.write_other γ y v (by rintro rfl; exact h hz)

/-- Key lemma for the lam/letin cases: opening the binder with a fresh `z` and
    then closing under `γ.write z va` equals closing the body under `γ` and then
    plugging `va` into the bound position. The merged single-env analogue of the
    old `substEnv_cons_openVar`. -/
theorem Exp.substEnv_write_openVar (e : Exp) (γ : REnv) (va : Val) (z : EVar) (k : Nat)
    (hz_fv : z ∉ e.fv) (hγ : ∀ w ∈ e.fv, Val.lc (γ.map w)) :
    Exp.substEnv (γ.write z va) (Exp.openVar k z e) =
      Exp.openExp k va.toExp (Exp.substEnv γ e) := by
  induction e generalizing k with
  | bvar j =>
    by_cases hjk : j = k
    · subst hjk; simp [Exp.openVar, Exp.substEnv, Exp.openExp]
    · simp [Exp.openVar, Exp.substEnv, Exp.openExp, hjk]
  | iconst _ | bconst _ => rfl
  | fvar y =>
    have hyz : z ≠ y := fun he => hz_fv (by simp [Exp.fv, he])
    show Exp.substEnv (γ.write z va) (.fvar y) = Exp.openExp k va.toExp ((γ.map y).toExp)
    rw [Exp.substEnv_fvar, REnv.write_other γ z va hyz]
    exact (Exp.openExp_of_lc_at _ k va.toExp
      (Exp.lc_at_mono _ (Nat.zero_le k)
        (Val.toExp_lc_at_zero (hγ y (by simp [Exp.fv]))))).symm
  | lam e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih (k+1) (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | ann e t ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | not e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ (k+1) hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    obtain ⟨⟨hz₀, hz₁⟩, hz₂⟩ := hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₀ k hz₀ (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₁ k hz₁ (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz₂ (fun w hw => hγ w (by simp [Exp.fv, hw]))]

/-- `write` (on the name map) commutes with `push` (on the de Bruijn stack):
    they touch disjoint fields of `REnv`. -/
theorem REnv.push_write_comm (γ : REnv) (w : Val) (x : EVar) (v : Val) :
    (γ.write x v).push w = (γ.push w).write x v := by
  apply REnv.ext <;> rfl

/-- `update` (a `write` of an injected value) likewise commutes with `push`. -/
theorem REnv.push_update_comm (γ : REnv) (w : Val) (b : Base) (x : EVar) (v : b.interp) :
    (γ.update b x v).push w = (γ.push w).update b x v :=
  REnv.push_write_comm γ w x (Val.inj b v)


/-! ## Rename keystone: interpretation

  Under the single-map `REnv`, renaming `x → y` corresponds to copying `y`'s
  (single) cell into `x` with the Val-level `write`. (The old two-field version
  set `x`'s int- and bool-slots independently to `y`'s; that has no single-map
  analogue, since one cell cannot hold both an `Int` and a `Bool` at once.) -/

theorem REnv.get_write_other (b : Base) (γ : REnv) (x : EVar) (v : Val) {y : EVar}
    (h : x ≠ y) : REnv.get b (γ.write x v) y = REnv.get b γ y := by
  have hxy : (x == y) = false := by simp [h]
  simp [REnv.get, REnv.lookup, hxy]

/-! ## write-at-fresh-variable invariance of interpretation

  Writing *any* `Val` at a name not occurring in a term/formula leaves its
  interpretation unchanged. Generalizes `interp_update_fresh_*` to arbitrary
  written values (incl. closures) — needed because the merged extension
  `γ.write`.write may store a closure at a fresh higher-order binder. -/

theorem Term.interp_write_fresh {b : Base} (t : Term b)
    (x : EVar) (v : Val) (γ : REnv) (h : x ∉ t.fv) :
    Term.interp (γ.write x v) t = Term.interp γ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    have hxy : x ≠ y := fun he => h (by subst he; simp [Term.fv])
    exact REnv.get_write_other bv γ x v hxy
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]
  | not t ih => simp only [Term.interp, ih h]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]

theorem Formula.interp_write_fresh (φ : Formula)
    (x : EVar) (v : Val) (γ : REnv)
    (hfv : x ∉ φ.fv) :
    Formula.interp (γ.write x v) φ ↔ Formula.interp γ φ := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  induction φ generalizing γ with
  | tt => simp [Formula.interp]
  | ff => simp [Formula.interp]
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp,
      Term.interp_write_fresh t₁ x v γ (not_mem_l _ _ _ hfv),
      Term.interp_write_fresh t₂ x v γ (not_mem_r _ _ _ hfv)]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hfv
    simp only [Formula.interp, ih₁ γ hfv.1, ih₂ γ hfv.2]
  | not φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    exact not_congr (ih γ hfv)
  | ex _ φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    refine exists_congr (fun n => ?_)
    rw [REnv.push_write_comm]
    exact ih (γ.push _) hfv
  | all _ φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    refine forall_congr' (fun n => ?_)
    rw [REnv.push_write_comm]
    exact ih (γ.push _) hfv

/-! ## ν-instantiation

  `instNu x r` replaces ν (`Term.bvar _ 0`) throughout `r` with the free name
  `x`, and *shifts every deeper de Bruijn index down by one* (proper LN binder
  instantiation). The shift is what makes the model-level bridge
  `interp (r.instNu x) (γ.update x v) = interp r (γ.push v)` hold for *every*
  `r` (given `x ∉ r.fv`), rather than only ν-closed ones — see
  `Refinement.interp_instNu`. This is the refinement-level analogue of
  `Ty.openVar`: it opens the ν binder to a free name, and is what lets
  `Subtyp.refine` be stated in *opened* form (mirroring `Subtyp.arrow`). -/
def Term.instNuAt (k : Nat) (x : EVar) : {b : Base} → Term b → Term b
  | _, .const b c => .const b c
  | _, .bvar b j  =>
      if j = k then .fvar b x
      else if k < j then .bvar b (j - 1) else .bvar b j
  | _, .fvar b y  => .fvar b y
  | _, .add t₁ t₂ => .add (t₁.instNuAt k x) (t₂.instNuAt k x)
  | _, .not t     => .not (t.instNuAt k x)
  | _, .and t₁ t₂ => .and (t₁.instNuAt k x) (t₂.instNuAt k x)

def Formula.instNuAt (k : Nat) (x : EVar) : Formula → Formula
  | .tt         => .tt
  | .ff         => .ff
  | .eq b t₁ t₂ => .eq b (t₁.instNuAt k x) (t₂.instNuAt k x)
  | .leqI t₁ t₂ => .leqI (t₁.instNuAt k x) (t₂.instNuAt k x)
  | .and φ₁ φ₂  => .and (φ₁.instNuAt k x) (φ₂.instNuAt k x)
  | .or φ₁ φ₂   => .or (φ₁.instNuAt k x) (φ₂.instNuAt k x)
  | .not φ      => .not (φ.instNuAt k x)
  | .imp φ₁ φ₂  => .imp (φ₁.instNuAt k x) (φ₂.instNuAt k x)
  | .ex b φ     => .ex b (φ.instNuAt (k + 1) x)
  | .all b φ    => .all b (φ.instNuAt (k + 1) x)

/-- Instantiate ν (`bvar 0`) of a refinement to the free name `x`. -/
def Refinement.instNu (x : EVar) : Refinement → Refinement
  | .fmla φ       => .fmla (φ.instNuAt 0 x)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, a.2.instNuAt 0 x⟩))

/-! ### Model-level bridge: instantiation = push

  `push` is `insertBV 0`; interpreting through a `write`-updated name map after
  ν-instantiation agrees with interpreting through a `push`ed de Bruijn slot. We
  prove the general `insertBV k` form so the induction goes under `Formula`
  quantifiers. -/

theorem REnv.write_push (γ : REnv) (x : EVar) (w u : Val) :
    (γ.write x w).push u = (γ.push u).write x w := rfl

theorem Term.interp_instNuAt {b : Base} (x : EVar) (w : Val) :
    ∀ (t : Term b) (γ : REnv) (k : Nat),
      k ≤ γ.bv.length → x ∉ t.fv →
      Term.interp (γ.write x w) (t.instNuAt k x) = Term.interp (γ.insertBV k w) t := by
  intro t
  induction t with
  | const b c => intro γ k _ _; rfl
  | bvar b j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.instNuAt, Term.interp, REnv.get, REnv.lookup,
          REnv.write, beq_self_eq_true, if_true, REnv.getBV, REnv.insertBV_bv,
          List.getElem?_insertIdx_self, hk, if_true, Option.getD_some]
      · simp only [Term.instNuAt, if_neg hjk, Term.interp, REnv.getBV,
          REnv.insertBV_bv]
        by_cases hlt : k < j
        · rw [if_pos hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_lt (by omega)]
  | fvar b y =>
      intro γ k _ hx
      simp only [Term.fv, List.mem_singleton] at hx
      simp only [Term.instNuAt, Term.interp, REnv.get, REnv.lookup, REnv.write,
        REnv.insertBV_map, beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, if_false]
  | add t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.instNuAt, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | not t ih =>
      intro γ k hk hx
      simp only [Term.fv] at hx
      simp only [Term.instNuAt, Term.interp, ih γ k hk hx]
  | and t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.instNuAt, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]

theorem Formula.interp_instNuAt (x : EVar) (w : Val) :
    ∀ (φ : Formula) (γ : REnv) (k : Nat),
      k ≤ γ.bv.length → x ∉ φ.fv →
      (Formula.interp (γ.write x w) (φ.instNuAt k x) ↔ Formula.interp (γ.insertBV k w) φ) := by
  intro φ
  induction φ with
  | tt => intro γ k _ _; simp [Formula.instNuAt, Formula.interp]
  | ff => intro γ k _ _; simp [Formula.instNuAt, Formula.interp]
  | eq b t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.instNuAt, Formula.interp,
        Term.interp_instNuAt x w t₁ γ k hk hx.1,
        Term.interp_instNuAt x w t₂ γ k hk hx.2]
  | leqI t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.instNuAt, Formula.interp,
        Term.interp_instNuAt x w t₁ γ k hk hx.1,
        Term.interp_instNuAt x w t₂ γ k hk hx.2]
  | and φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.instNuAt, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | or φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.instNuAt, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | not φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.instNuAt, Formula.interp, ih γ k hk hx]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.instNuAt, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | ex b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.instNuAt, Formula.interp]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push] at hv
        rw [REnv.push_insertBV_comm]
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp hv
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push]
        rw [REnv.push_insertBV_comm] at hv
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr hv
  | all b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.instNuAt, Formula.interp]
      constructor
      · intro h v
        rw [REnv.push_insertBV_comm]
        have := h v
        rw [REnv.write_push] at this
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp this
      · intro h v
        rw [REnv.write_push]
        have := h v
        rw [REnv.push_insertBV_comm] at this
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr this

/-- Model-level bridge: interpreting the ν-instantiated refinement against a
    name-map slot equals interpreting the original against a pushed de Bruijn
    slot. This is what lets the *opened* `Subtyp.refine` (and the *named* `.all`
    binder the generator emits) discharge the same VC the `push`-based form did. -/
theorem Refinement.interp_instNu (κ : KEnv) (r : Refinement) (γ : REnv)
    (x : EVar) (w : Val) (hx : x ∉ r.fv) :
    Refinement.interp κ (r.instNu x) (γ.write x w) ↔
    Refinement.interp κ r (γ.push w) := by
  cases r with
  | fmla φ =>
      simp only [Refinement.instNu, Refinement.interp]
      have := Formula.interp_instNuAt x w φ γ 0 (Nat.zero_le _) (by simpa [Refinement.fv] using hx)
      simpa [REnv.insertBV_zero] using this
  | kapp kn args =>
      have hmap :
          (List.map (fun a => (⟨a.1, Term.interp (γ.write x w) a.2⟩ : Σ b : Base, b.interp))
            (List.map (fun a => (⟨a.1, a.2.instNuAt 0 x⟩ : Σ b : Base, Term b)) args))
          = List.map (fun a => (⟨a.1, Term.interp (γ.push w) a.2⟩ : Σ b : Base, b.interp)) args := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a ha
        have hxa : x ∉ Term.fv a.2 := by
          simp only [Refinement.fv] at hx
          exact fun h => hx (List.mem_flatMap.mpr ⟨a, ha, h⟩)
        have h := Term.interp_instNuAt x w a.2 γ 0 (Nat.zero_le _) hxa
        rw [REnv.insertBV_zero] at h
        simp only [Function.comp_apply, h]
      simp only [Refinement.instNu, Refinement.interp, hmap]

end STLC
