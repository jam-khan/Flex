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
  has its ν (`bvar 0`) *opened* to the enclosing binder name `x` via
  `Refinement.openBVar 0` (defined in `Substitution.lean`) at generation time —
  the same opening `Subtyp.refine` uses declaratively.
-/

/-- The interpreted form of a constraint: a `κ`-indexed predicate over runtime
    environments. -/
@[simp]
abbrev Constraint := KEnv → REnv → Prop

namespace STLC

/-- Implication-constraint helper: bind `x` to a value satisfying refinement
    `r` (under `κ`), then assert `c`. For function-typed bindings, no
    quantification. The refinement's ν is instantiated to the fresh name `x`. -/
def implyBindCstr (x : EVar) (t : Ty) (c : Cstr) : Cstr :=
  match t with
  | .refine b r => .all x b (.imp (r.openBVar 0 x) c)
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
    exact h v ((Refinement.interp_openBVar κ r γ x (Val.inj b v) 0 (Nat.zero_le _) hx).mpr hr)
  · intro hr
    exact h v ((Refinement.interp_openBVar κ r γ x (Val.inj b v) 0 (Nat.zero_le _) hx).mp hr)

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

end STLC

/-! ## Algorithmic subtyping / bidirectional checking -/

/-- Algorithmic subtyping. Returns `none` on shape mismatch. Termination
    by `Ty.skel` (preserved under `openVar`). Takes `Γ` so the fresh name
    for the arrow / base cases is picked away from the context domain. -/
def sub (Γ : TEnv) : Ty → Ty → Option Cstr
  | .refine .int  r₁, .refine .int  r₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv)
      some (.all x .int (.imp (r₁.openBVar 0 x) (.head (r₂.openBVar 0 x))))
  | .refine .bool r₁, .refine .bool r₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv)
      some (.all x .bool (.imp (r₁.openBVar 0 x) (.head (r₂.openBVar 0 x))))
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
