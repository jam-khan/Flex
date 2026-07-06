import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Substitution
import Flex.VCG.STLC.Typing
import Flex.VCG.STLC.Notation

open STLC

/-! # VC Generation for STLC (LN + deep Formula + κ)

  Algorithmic bidirectional refinement type-checker that produces a *syntactic*
  constraint `Cstr` — a Constrained Horn Clause tree with constructors

  * `.head r`   — a goal refinement to prove,
  * `.imp r c`  — a hypothesis refinement guarding `c`,
  * `.all x b c`— a universally-quantified binder naming `x : b`,
  * `.conj c₁ c₂`— conjunction.

  `Cstr` is declared in `Syntax.lean`; its interpretation `Cstr.interp` (in
  `Model.lean`) reads a `Cstr` back as a `KEnv → REnv → Prop` (the `Constraint`
  abbrev). The user existentially quantifies the `KEnv` parameter to invoke the
  solver (`solve_fixpoint`); `topVC` is stated over `Cstr.interp`.

  Binders are *named* (textbook Horn / liquid-fixpoint form): `.all x b c`
  interprets as `∀ v:b, c[x ↦ v]`, updating the `REnv` name map at `x` (the de
  Bruijn stack stays empty). A refinement placed into a `.imp`/`.head` therefore
  has its ν (`bvar 0`) *instantiated* to the enclosing binder name `x` via
  `Refinement.instNu` at generation time.
-/

/-- The interpreted form of a constraint: a `κ`-indexed predicate over runtime
    environments. -/
@[simp]
abbrev Constraint := KEnv → REnv → Prop

namespace STLC

/-! ## ν-instantiation

  `instNu x r` replaces ν (`Term.bvar _ 0`) throughout `r` with the free name
  `x`, and *shifts every deeper de Bruijn index down by one* (proper LN binder
  instantiation). The shift is what makes the model-level bridge
  `interp (r.instNu x) (γ.update x v) = interp r (γ.push v)` hold for *every*
  `r` (given `x ∉ r.fv`), rather than only ν-closed ones — see
  `Refinement.interp_instNu`. On the refinements the generator actually feeds it
  (already opened over every enclosing arrow binder, so ν is their only bound
  index) the shift is a no-op. -/
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
    slot. This is what lets a *named* `.all` binder discharge the same VC the
    old `push`-based `implyBind` did. -/
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

/-- Implication-constraint helper: bind `x` to a value satisfying refinement
    `r` (under `κ`), then assert `c`. For function-typed bindings, no
    quantification. The refinement's ν is instantiated to the fresh name `x`. -/
def implyBindCstr (x : EVar) (t : Ty) (c : Cstr) : Cstr :=
  match t with
  | .refine b r => .all x b (.imp (r.instNu x) c)
  | .arrow _ _  => c

/-- Bridge: `implyBindCstr` over a refined binding interprets exactly as the old
    `push`-based `implyBind` (provided `x` is fresh for `r`). -/
theorem implyBindCstr_interp (κ : KEnv) (x : EVar) (b : Base) (r : Refinement)
    (c : Cstr) (γ : REnv) (hx : x ∉ r.fv) :
    (implyBindCstr x (.refine b r) c).interp κ γ ↔
    ∀ v : b.interp, Refinement.interp κ r (γ.push (Val.inj b v)) →
      c.interp κ (REnv.update b γ x v) := by
  simp only [implyBindCstr, Cstr.interp]
  constructor <;> intro h v
  · intro hr
    exact h v ((Refinement.interp_instNu κ r γ x (Val.inj b v) hx).mpr hr)
  · intro hr
    exact h v ((Refinement.interp_instNu κ r γ x (Val.inj b v) hx).mp hr)

/-- Semantic (`push`-form) reading of a bind, matching the pre-refactor
    `implyBind`. Used to keep the soundness proofs' `cases s` structure. -/
def implyBindSem (κ : KEnv) (x : EVar) (t : Ty) (c : Cstr) (γ : REnv) : Prop :=
  match t with
  | .refine b r => ∀ v : b.interp,
                     Refinement.interp κ r (γ.push (Val.inj b v)) →
                       c.interp κ (REnv.update b γ x v)
  | .arrow _ _  => c.interp κ γ

/-- `implyBindCstr` interprets as `implyBindSem`, for *any* binding type
    (provided `x` is fresh for the binding's refinement). -/
theorem implyBindCstr_interp_gen (κ : KEnv) (x : EVar) (t : Ty) (c : Cstr)
    (γ : REnv) (hx : x ∉ t.fv) :
    (implyBindCstr x t c).interp κ γ ↔ implyBindSem κ x t c γ := by
  cases t with
  | refine b r =>
      exact implyBindCstr_interp κ x b r c γ (by simpa [Ty.fv] using hx)
  | arrow s t => simp only [implyBindCstr, implyBindSem]

/-- Bridge for the subtyping base case: the generated `∀/⇒/head` constraint
    interprets as the `push`-form entailment `Subtyp.refine` expects. -/
theorem sub_refine_interp (κ : KEnv) (x : EVar) (b : Base) (r₁ r₂ : Refinement)
    (γ : REnv) (hx₁ : x ∉ r₁.fv) (hx₂ : x ∉ r₂.fv) :
    (Cstr.all x b (.imp (r₁.instNu x) (.head (r₂.instNu x)))).interp κ γ ↔
    ∀ v : b.interp, Refinement.interp κ r₁ (γ.push (Val.inj b v)) →
      Refinement.interp κ r₂ (γ.push (Val.inj b v)) := by
  simp only [Cstr.interp]
  constructor <;> intro h v hr
  · exact (Refinement.interp_instNu κ r₂ γ x (Val.inj b v) hx₂).mp
      (h v ((Refinement.interp_instNu κ r₁ γ x (Val.inj b v) hx₁).mpr hr))
  · exact (Refinement.interp_instNu κ r₂ γ x (Val.inj b v) hx₂).mpr
      (h v ((Refinement.interp_instNu κ r₁ γ x (Val.inj b v) hx₁).mp hr))

end STLC

/-! ## Algorithmic subtyping / bidirectional checking -/

/-- Algorithmic subtyping. Returns `none` on shape mismatch. Termination
    by `Ty.skel` (preserved under `openVar`). Takes `Γ` so the fresh name
    for the arrow / base cases is picked away from the context domain. -/
def sub (Γ : TEnv) : Ty → Ty → Option Cstr
  | .refine .int  r₁, .refine .int  r₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv)
      some (.all x .int (.imp (r₁.instNu x) (.head (r₂.instNu x))))
  | .refine .bool r₁, .refine .bool r₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv)
      some (.all x .bool (.imp (r₁.instNu x) (.head (r₂.instNu x))))
  | .arrow s₁ t₁, .arrow s₂ t₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ
                            ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv)
      match sub Γ s₂ s₁, sub ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) with
      | some c₁, some c₂ =>
          some (.conj c₁ (implyBindCstr x s₂ c₂))
      | _, _ => none
  | _, _ => none
termination_by s t => s.skel + t.skel
decreasing_by all_goals
  first
    | (simp_wf; simp only [Ty.skel, Ty.skel_openVar]; omega)
    | (simp only [Ty.skel, Ty.skel_openVar]; omega)
    | omega

mutual
  def synth (Γ : TEnv) : Exp → Option (Cstr × Ty)
    | .fvar x    => Γ.lookup x |>.map (fun t => (Cstr.triv, self x t))
    | .iconst n  => some (Cstr.triv, prim n)
    | .bconst b  => some (Cstr.triv, primBool b)
    | .ann e t =>
        match check Γ e t with
        | some c => some (c, t)
        | none   => none
    | .app e₁ (.fvar y) =>
        match synth Γ e₁ with
        | some (c, .arrow s t) =>
            -- Hygiene: `y` must not capture into `t` when we open `t.openVar 0 y`.
            if y ∈ t.fv then none
            else
              match check Γ (.fvar y) s with
              | some c' => some (Cstr.conj c c', t.openVar 0 y)
              | none    => none
        | _ => none
    | .leq (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some (Cstr.triv, <ty| Bool{ν : (ν = true → x ≤ y) ∧ (x ≤ y → ν = true)} |>)
        | _, _ => none
    | .add (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some (Cstr.triv, <ty| Int{ν : ν = x + y}|>)
        | _, _ => none
    | .not (.fvar x) =>
        match Γ.lookup x with
        | some (.refine .bool _) => some (Cstr.triv, <ty| Bool{ν : ν = ¬x}|>)
        | _ => none
    | .and (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .bool _), some (.refine .bool _) =>
            some (Cstr.triv, <ty| Bool{ν : ν = x ∧ y} |>)
        | _, _ => none
    | _ => none
  termination_by e => 2 * e.skel
  decreasing_by all_goals
    (first | (simp only [Exp.skel]; omega) | omega)


  def check (Γ : TEnv) : Exp → Ty → Option Cstr
    | .lam e, .arrow s₁ s₂ =>
        let x := EVar.fresh (TEnv.dom Γ ++ e.fv ++ s₁.fv ++ s₂.fv ++ TEnv.tyFv Γ)
        match check ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) with
        | some c => some (implyBindCstr x s₁ c)
        | none   => none
    | .letin e₁ e₂, t =>
        match synth Γ e₁ with
        | some (c₁, s) =>
            let x := EVar.fresh (TEnv.dom Γ ++ e₂.fv ++ s.fv ++ t.fv ++ TEnv.tyFv Γ)
            match check ((x, s) :: Γ) (e₂.openVar 0 x) t with
            | some c₂ => some (Cstr.conj c₁ (implyBindCstr x s c₂))
            | none    => none
        | none => none
    | .ite e₀ e₁ e₂, t =>
        match e₀ with
        | .fvar x =>
              match Γ.lookup x with
              | some (.refine .bool _) =>
                  -- Fresh guard variable `y` (standard `if`-rule): keep `x : {ν|r}` in
                  -- scope and add the path condition `x = true/false` via a fresh
                  -- binding whose refinement mentions `x` free. This preserves `r`
                  -- in each branch without conjoining into the (atomic) refinement.
                  let y := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ
                                        ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x])
                  let r_true  : Ty := <ty| Bool{ν : x = true}|>
                  let r_false : Ty := <ty| Bool{ν : x = false}|>
                  match check ((y, r_true) :: Γ) e₁ t,
                        check ((y, r_false) :: Γ) e₂ t with
                  | some c₁, some c₂ =>
                      some (Cstr.conj (implyBindCstr y r_true  c₁)
                                      (implyBindCstr y r_false c₂))
                  | _, _ => none
              | _ => none
        | _ => none
    | e, t =>
        -- Catch-all (Chk-Syn): synthesize, then subtype.
        match synth Γ e with
        | some (c, s) =>
            match sub Γ s t with
            | some c' => some (Cstr.conj c c')
            | none    => none
        | none => none
  termination_by e _ => 2 * e.skel + 1
  decreasing_by all_goals
    (first | (simp only [Exp.skel, Exp.skel_openVar]; omega) | omega)
end

/-- Top-level: produce a closed Lean `Prop` (parameterized by a κ-assignment)
    to hand to `solve_fixpoint`. The user writes `∃ κ, topVC κ [] e t`. -/
@[simp]
def topVC (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) : Prop :=
  match check Γ e t with
  | some c => ∀ γ : REnv, c.interp κ γ
  | none   => False
