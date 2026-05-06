import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Typing

open STLC

-- VC Generation for STLC

@[simp]
abbrev Constraint := REnv → Prop

-- Implication-constraint helper from page 17 of the refinement-types tutorial.
@[simp, reducible]
def implyBind (x : EVar) (t : Ty) (c : Constraint) : Constraint :=
  match t with
  | .refine b r => fun ρ => ∀ v : b.interp, r.pred ρ v → c (REnv.update b ρ x v)
  | .arrow ..   => c

-- Algorithmic subtyping. Returns `none` on shape mismatch.
def sub (x : Ty) (y : Ty) : Option Constraint :=
  match x, y with
    | .refine .int r₁, .refine .int r₂ =>
        some (fun ρ => ∀ v : Int, r₁.pred ρ v → r₂.pred ρ v)
    | .refine .bool r₁, .refine .bool r₂ =>
        some (fun ρ => ∀ v : Bool, r₁.pred ρ v → r₂.pred ρ v)
    | .arrow x₁ s₁ t₁, .arrow x₂ s₂ t₂ =>
        match sub s₂ s₁, sub (t₁.rename x₁ x₂) t₂ with
        | some c₁, some c₂ =>
            some (fun ρ => c₁ ρ ∧ implyBind x₂ s₂ c₂ ρ)
        | _, _ => none
    | _, _ => none
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := Ty.sizeOf_rename x₁ x₂ t₁; omega)

-- One-step unfolding equations (no recursion in RHS) — used in soundness proofs.
@[simp]
theorem sub_refine_int_refine_int_eq (r₁ r₂ : Refinement .int) :
    sub (.refine .int r₁) (.refine .int r₂) =
      some (fun ρ => ∀ v : Int, r₁.pred ρ v → r₂.pred ρ v) := by
  unfold sub; rfl

@[simp]
theorem sub_refine_bool_refine_bool_eq (r₁ r₂ : Refinement .bool) :
    sub (.refine .bool r₁) (.refine .bool r₂) =
      some (fun ρ => ∀ v : Bool, r₁.pred ρ v → r₂.pred ρ v) := by
  unfold sub; rfl

@[simp]
theorem sub_refine_arrow_eq (b : Base) (r : Refinement b)
    (x : EVar) (s t : Ty) :
    sub (.refine b r) (.arrow x s t) = none := by
  unfold sub; cases b <;> rfl

@[simp]
theorem sub_arrow_refine_eq (x : EVar) (s t : Ty)
    (b : Base) (r : Refinement b) :
    sub (.arrow x s t) (.refine b r) = none := by
  unfold sub; rfl

mutual
  def synth (Γ : TEnv) : Exp → Option (Constraint × Ty)
    | .var x    => Γ.lookup x |>.map (fun t => ((fun _ => True), self x t))
    | .iconst n => some ((fun _ => True), prim n)
    | .bconst b => some ((fun _ => True), primBool b)
    | .ann e t =>
        match check Γ e t with
        | some c => some (c, t)
        | none   => none
    | .app e₁ (.var y) =>
        match synth Γ e₁ with
        | some (c, .arrow x s t) =>
            match check Γ (.var y) s with
            | some c' => some ((fun ρ => c ρ ∧ c' ρ), t.rename x y)
            | none    => none
        | _ => none
    | _ => none
  termination_by e => 2 * sizeOf e

  def check (Γ : TEnv) : Exp → Ty → Option Constraint
    | .lam x e, .arrow x' s t =>
        -- Same-binder convention: alpha-renaming is the user's responsibility.
        if x == x' then
          match check ((x, s) :: Γ) e t with
          | some c => some (implyBind x s c)
          | none   => none
        else none
    | .letin x e₁ e₂, t =>
        match synth Γ e₁ with
        | some (c₁, s) =>
            match check ((x, s) :: Γ) e₂ t with
            | some c₂ => some (fun ρ => c₁ ρ ∧ implyBind x s c₂ ρ)
            | none    => none
        | none => none
    | e, t =>
        -- Catch-all (Chk-Syn): synthesize, then subtype.
        match synth Γ e with
        | some (c, s) =>
            match sub s t with
            | some c' => some (fun ρ => c ρ ∧ c' ρ)
            | none    => none
        | none => none
  termination_by e _ => 2 * sizeOf e + 1
end

-- Top-level: produce a closed Lean `Prop` to hand to `solve_fixpoint`.
@[simp]
def topVC (Γ : TEnv) (e : Exp) (t : Ty) : Prop :=
  match check Γ e t with
  | some c => ∀ ρ : REnv, c ρ
  | none   => False
