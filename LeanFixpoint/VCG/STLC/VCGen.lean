import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution
import LeanFixpoint.VCG.STLC.Typing

open STLC

/-! # VC Generation for STLC (LN + deep Formula + κ)

  Algorithmic bidirectional refinement type-checker that produces a
  `Constraint : REnv → Prop`.

-/

@[simp]
abbrev Constraint := REnv → Prop

/-- Implication-constraint helper: bind `x` to a value satisfying refinement
    `r` (under `κ`), then assert `c` holds. For function-typed bindings, no
    quantification. -/
@[simp, reducible]
def implyBind (κ : KEnv) (x : EVar) (t : Ty) (c : Constraint) : Constraint :=
  fun ρ =>
    match t with
    | .refine b r => ∀ v : b.interp,
                       Refinement.interp κ r ρ v → c (REnv.update b ρ x v)
    | .arrow _ _  => c ρ

/-- Algorithmic subtyping. Returns `none` on shape mismatch. Termination
    by `Ty.skel` (preserved under `openVar`). Takes `Γ` so the fresh name
    for the arrow case is picked away from the context domain. -/
def sub (κ : KEnv) (Γ : TEnv) : Ty → Ty → Option Constraint
  | .refine .int  r₁, .refine .int  r₂ =>
      some (fun ρ => ∀ v : Int,
              Refinement.interp κ r₁ ρ v → Refinement.interp κ r₂ ρ v)
  | .refine .bool r₁, .refine .bool r₂ =>
      some (fun ρ => ∀ v : Bool,
              Refinement.interp κ r₁ ρ v → Refinement.interp κ r₂ ρ v)
  | .arrow s₁ t₁, .arrow s₂ t₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ
                            ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv
                            ++ Ty.named s₁ ++ Ty.named s₂
                            ++ Ty.named t₁ ++ Ty.named t₂ ++ [nuName])
      match sub κ Γ s₂ s₁, sub κ ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) with
      | some c₁, some c₂ =>
          some (fun ρ => c₁ ρ ∧ implyBind κ x s₂ c₂ ρ)
      | _, _ => none
  | _, _ => none
termination_by s t => s.skel + t.skel
decreasing_by all_goals
  first
    | (simp_wf; simp only [Ty.skel, Ty.skel_openVar]; omega)
    | (simp only [Ty.skel, Ty.skel_openVar]; omega)
    | omega

mutual
  def synth (κ : KEnv) (Γ : TEnv) : Exp → Option (Constraint × Ty)
    | .fvar x    => Γ.lookup x |>.map (fun t => ((fun _ => True), self x t))
    | .iconst n  => some ((fun _ => True), prim n)
    | .bconst b  => some ((fun _ => True), primBool b)
    | .ann e t =>
        match check κ Γ e t with
        | some c => some (c, t)
        | none   => none
    | .app e₁ (.fvar y) =>
        match synth κ Γ e₁ with
        | some (c, .arrow s t) =>
            -- Hygiene: `y` must not capture into `t` when we open `t.openVar 0 y`.
            if y ∈ t.fv ∨ y ∈ Ty.named t ∨ y = nuName then none
            else
              match check κ Γ (.fvar y) s with
              | some c' => some ((fun ρ => c ρ ∧ c' ρ), t.openVar 0 y)
              | none    => none
        | _ => none
    | .leq (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some ((fun _ => True),
              .refine .bool ⟨.and
                (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
                      (.leqI (.fvar .int x) (.fvar .int y)))
                (.imp (.leqI (.fvar .int x) (.fvar .int y))
                      (.eqB (.fvar .bool nuName) (.const .bool true)))⟩)
        | _, _ => none
    | .add (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some ((fun _ => True),
              .refine .int ⟨.eqI (.fvar .int nuName)
                                 (.add (.fvar .int x) (.fvar .int y))⟩)
        | _, _ => none
    | .not (.fvar x) =>
        match Γ.lookup x with
        | some (.refine .bool _) =>
            some ((fun _ => True),
              .refine .bool ⟨.eqB (.fvar .bool nuName) (.not (.fvar .bool x))⟩)
        | _ => none
    | .and (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .bool _), some (.refine .bool _) =>
            some ((fun _ => True),
              .refine .bool ⟨.eqB (.fvar .bool nuName) (.and (.fvar .bool x) (.fvar .bool y))⟩)
        | _, _ => none
    | _ => none
  termination_by e => 2 * e.skel
  decreasing_by all_goals
    (first | (simp only [Exp.skel]; omega) | omega)


  def check (κ : KEnv) (Γ : TEnv) : Exp → Ty → Option Constraint
    | .lam e, .arrow s₁ s₂ =>
        let x := EVar.fresh (TEnv.dom Γ ++ e.fv ++ s₁.fv ++ s₂.fv
                              ++ Ty.named s₁ ++ Ty.named s₂
                              ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
        match check κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) with
        | some c => some (implyBind κ x s₁ c)
        | none   => none
    | .letin e₁ e₂, t =>
        match synth κ Γ e₁ with
        | some (c₁, s) =>
            let x := EVar.fresh (TEnv.dom Γ ++ e₂.fv ++ s.fv ++ t.fv
                                  ++ Ty.named s ++ Ty.named t
                                  ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
            match check κ ((x, s) :: Γ) (e₂.openVar 0 x) t with
            | some c₂ => some (fun ρ => c₁ ρ ∧ implyBind κ x s c₂ ρ)
            | none    => none
        | none => none
    | .ite e₀ e₁ e₂, t =>
        match e₀ with
        | .fvar x =>
            -- Hygiene: `x` must not clash with the ν-reserved name.
            if x = nuName then none
            else
              match Γ.lookup x with
              | some (.refine .bool r) =>
                  let r_true  : Ty := .refine .bool ⟨.and r.fmla
                    (.eqB (.fvar .bool nuName) (.const .bool true))⟩
                  let r_false : Ty := .refine .bool ⟨.and r.fmla
                    (.eqB (.fvar .bool nuName) (.const .bool false))⟩
                  match check κ ((x, r_true) :: Γ) e₁ t,
                        check κ ((x, r_false) :: Γ) e₂ t with
                  | some c₁, some c₂ =>
                      some (fun ρ =>
                        implyBind κ x r_true  c₁ ρ ∧
                        implyBind κ x r_false c₂ ρ)
                  | _, _ => none
              | _ => none
        | _ => none
    | e, t =>
        -- Catch-all (Chk-Syn): synthesize, then subtype.
        match synth κ Γ e with
        | some (c, s) =>
            match sub κ Γ s t with
            | some c' => some (fun ρ => c ρ ∧ c' ρ)
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
  match check κ Γ e t with
  | some c => ∀ ρ : REnv, c ρ
  | none   => False
