import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution
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
        if x₁ == x₂ then
          match sub s₂ s₁, sub t₁ t₂ with
          | some c₁, some c₂ =>
              some (fun ρ => c₁ ρ ∧ implyBind x₁ s₂ c₂ ρ)
          | _, _ => none
        else none
    | _, _ => none
termination_by sizeOf x + sizeOf y
decreasing_by all_goals simp_wf; omega

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
    | .leq (.var x) (.var y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some ((fun _ => True),
              .refine .bool {
                int_fv := [x, y], bool_fv := [], pred := fun ρ v => v = decide (ρ.ints x ≤ ρ.ints y),
                ext := by intro ρ₁ ρ₂ v h_int _h_bool
                          have hx := h_int x (by simp)
                          have hy := h_int y (by simp)
                          simp [hx, hy] })
        | _, _ => none
    | .add (.var x) (.var y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some ((fun _ => True),
              .refine .int {
                int_fv := [x, y], bool_fv := [], pred := fun ρ v => v = ρ.ints x + ρ.ints y,
                ext := by intro ρ₁ ρ₂ v h_int _h_bool
                          have hx := h_int x (by simp)
                          have hy := h_int y (by simp)
                          simp [hx, hy] })
        | _, _ => none
    | .not e =>
        match synth Γ e with
        | some (c, .refine .bool r) =>
            some (c, .refine .bool {
              int_fv := r.int_fv, bool_fv := r.bool_fv,
              pred := fun ρ v => ∃ b, r.pred ρ b ∧ v = !b,
              ext := fun h_int h_bool =>
                ⟨fun ⟨bv, hb, hv⟩ => ⟨bv, (r.ext h_int h_bool).mp hb, hv⟩,
                 fun ⟨bv, hb, hv⟩ => ⟨bv, (r.ext h_int h_bool).mpr hb, hv⟩⟩ })
        | _ => none
    | .and e₁ e₂ =>
        match synth Γ e₁ with
        | some (c₁, .refine .bool r₁) =>
            match synth Γ e₂ with
            | some (c₂, .refine .bool r₂) =>
                some (fun ρ => c₁ ρ ∧ c₂ ρ,
                      .refine .bool
                        { int_fv := r₁.int_fv ++ r₂.int_fv, bool_fv := r₁.bool_fv ++ r₂.bool_fv,
                          pred := fun ρ v => ∃ b₁ b₂, r₁.pred ρ b₁ ∧ r₂.pred ρ b₂ ∧ v = (b₁ && b₂),
                          ext := fun h_int h_bool =>
                            have h₁_int := fun y hy => h_int y (List.mem_append_left _ hy)
                            have h₂_int := fun y hy => h_int y (List.mem_append_right _ hy)
                            have h₁_bool := fun y hy => h_bool y (List.mem_append_left _ hy)
                            have h₂_bool := fun y hy => h_bool y (List.mem_append_right _ hy)
                            ⟨fun ⟨b₁, b₂, hb₁, hb₂, hv⟩ =>
                               ⟨b₁, b₂, (r₁.ext h₁_int h₁_bool).mp hb₁, (r₂.ext h₂_int h₂_bool).mp hb₂, hv⟩,
                             fun ⟨b₁, b₂, hb₁, hb₂, hv⟩ =>
                               ⟨b₁, b₂, (r₁.ext h₁_int h₁_bool).mpr hb₁, (r₂.ext h₂_int h₂_bool).mpr hb₂, hv⟩⟩ })
            | _ => none
        | _ => none
    | _ => none
  termination_by e => 2 * sizeOf e


  def check (Γ : TEnv) : Exp → Ty → Option Constraint
    | .lam x e, .arrow x' s t =>
        -- Same-binder convention: alpha-renaming is the user's responsibility.
        -- Also reject shadowing: the binder must be fresh in Γ.
        if x == x' then
          match Γ.lookup x with
          | none =>
              match check ((x, s) :: Γ) e t with
              | some c => some (implyBind x s c)
              | none   => none
          | some _ => none
        else none
    | .letin x e₁ e₂, t =>
        match Γ.lookup x with
        | none =>
            match synth Γ e₁ with
            | some (c₁, s) =>
                match check ((x, s) :: Γ) e₂ t with
                | some c₂ => some (fun ρ => c₁ ρ ∧ implyBind x s c₂ ρ)
                | none    => none
            | none => none
        | some _ => none
    | .ite e₀ e₁ e₂, t =>
        match e₀ with
        | .var x =>
            match Γ.lookup x with
            | some (.refine .bool r) =>
                match check ((x, .refine .bool r.ite_true)  :: Γ) e₁ t,
                      check ((x, .refine .bool r.ite_false) :: Γ) e₂ t with
                | some c₁, some c₂ =>
                    some (fun ρ =>
                      implyBind x (.refine .bool r.ite_true)  c₁ ρ ∧
                      implyBind x (.refine .bool r.ite_false) c₂ ρ)
                | _, _ => none
            | _ => none
        | _ => none
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

-- One-step unfolding equations for synth cases — used in examples and soundness proofs.
-- `add_var` and `leq_var` are now conditional on operand lookups producing
-- int-refined types, so they take the lookup hypotheses explicitly.
theorem synth_add_var_eq (Γ : TEnv) (x y : EVar) {r₁ r₂ : Refinement .int}
    (hx : Γ.lookup x = some (.refine .int r₁))
    (hy : Γ.lookup y = some (.refine .int r₂)) :
    synth Γ (.add (.var x) (.var y)) =
      some ((fun _ => True), .refine .int {
        int_fv := [x, y], bool_fv := [], pred := fun ρ v => v = ρ.ints x + ρ.ints y,
        ext := by intro ρ₁ ρ₂ v h_int _h_bool
                  have hxi := h_int x (by simp)
                  have hyi := h_int y (by simp)
                  simp [hxi, hyi] }) := by
  simp [synth, hx, hy]

theorem synth_leq_var_eq (Γ : TEnv) (x y : EVar) {r₁ r₂ : Refinement .int}
    (hx : Γ.lookup x = some (.refine .int r₁))
    (hy : Γ.lookup y = some (.refine .int r₂)) :
    synth Γ (.leq (.var x) (.var y)) =
      some ((fun _ => True), .refine .bool {
        int_fv := [x, y], bool_fv := [], pred := fun ρ v => v = decide (ρ.ints x ≤ ρ.ints y),
        ext := by intro ρ₁ ρ₂ v h_int _h_bool
                  have hxi := h_int x (by simp)
                  have hyi := h_int y (by simp)
                  simp [hxi, hyi] }) := by
  simp [synth, hx, hy]

@[simp]
theorem synth_not_eq (Γ : TEnv) (e : Exp) :
    synth Γ (.not e) =
      match synth Γ e with
      | some (c, .refine .bool r) =>
          some (c, .refine .bool {
            int_fv := r.int_fv, bool_fv := r.bool_fv,
            pred := fun ρ v => ∃ b, r.pred ρ b ∧ v = !b,
            ext := fun h_int h_bool =>
              ⟨fun ⟨bv, hb, hv⟩ => ⟨bv, (r.ext h_int h_bool).mp hb, hv⟩,
               fun ⟨bv, hb, hv⟩ => ⟨bv, (r.ext h_int h_bool).mpr hb, hv⟩⟩ })
      | _ => none := by
  simp [synth]

@[simp]
theorem synth_and_eq (Γ : TEnv) (e₁ e₂ : Exp) :
    synth Γ (.and e₁ e₂) =
      match synth Γ e₁ with
      | some (c₁, .refine .bool r₁) =>
          match synth Γ e₂ with
          | some (c₂, .refine .bool r₂) =>
              some (fun ρ => c₁ ρ ∧ c₂ ρ,
                    .refine .bool
                      { int_fv := r₁.int_fv ++ r₂.int_fv, bool_fv := r₁.bool_fv ++ r₂.bool_fv,
                        pred := fun ρ v => ∃ b₁ b₂, r₁.pred ρ b₁ ∧ r₂.pred ρ b₂ ∧ v = (b₁ && b₂),
                        ext := fun h_int h_bool =>
                          have h₁_int := fun y hy => h_int y (List.mem_append_left _ hy)
                          have h₂_int := fun y hy => h_int y (List.mem_append_right _ hy)
                          have h₁_bool := fun y hy => h_bool y (List.mem_append_left _ hy)
                          have h₂_bool := fun y hy => h_bool y (List.mem_append_right _ hy)
                          ⟨fun ⟨b₁, b₂, hb₁, hb₂, hv⟩ =>
                             ⟨b₁, b₂, (r₁.ext h₁_int h₁_bool).mp hb₁, (r₂.ext h₂_int h₂_bool).mp hb₂, hv⟩,
                           fun ⟨b₁, b₂, hb₁, hb₂, hv⟩ =>
                             ⟨b₁, b₂, (r₁.ext h₁_int h₁_bool).mpr hb₁, (r₂.ext h₂_int h₂_bool).mpr hb₂, hv⟩⟩ })
          | _ => none
      | _ => none := by
  simp [synth]

-- Top-level: produce a closed Lean `Prop` to hand to `solve_fixpoint`.
@[simp]
def topVC (Γ : TEnv) (e : Exp) (t : Ty) : Prop :=
  match check Γ e t with
  | some c => ∀ ρ : REnv, c ρ
  | none   => False
