import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution
import LeanFixpoint.VCG.STLC.Entailment

open STLC

/-! ## Subtyping  Γ ⊢ s <: t -/

inductive Subtyp : TEnv → Ty → Ty → Prop where
  /-- SUB-BASE:  Γ ⊢ ∀v. p₁ ρ v → p₂ ρ v   ⟹   Γ ⊢ {ν:b|p₁} <: {ν:b|p₂} -/
  | refine {Γ b r₁ r₂} :
      Entail Γ (fun ρ => ∀ v : b.interp, r₁.pred ρ v → r₂.pred ρ v) →
      Subtyp Γ (.refine b r₁) (.refine b r₂)

  /-- SUB-FUN (same-binder form):
      contravariant input, covariant output under the shared binder. -/
  | arrow {Γ x s₁ t₁ s₂ t₂} :
      Subtyp Γ s₂ s₁ →
      Subtyp ((x, s₂) :: Γ) t₁ t₂ →
      Subtyp Γ (.arrow x s₁ t₁) (.arrow x s₂ t₂)

-- refinement type for an integer constant
@[simp]
def prim (n : Int) : Ty :=
  .refine .int ⟨[], fun _ v => v = n, fun _ => Iff.rfl⟩

-- refinement type for a boolean constant
@[simp]
def primBool (b : Bool) : Ty :=
  .refine .bool ⟨[], fun _ v => v = b, fun _ => Iff.rfl⟩

/-- `self x t` strengthens `t` with `v = REnv.get b ρ x`, tying the synthesized
    value back to the stored value of `x` in the environment. -/
@[simp]
def self : EVar → Ty → Ty
    | x, .refine b p    => .refine b ⟨p.fv ++ [x], fun ρ v => p.pred ρ v ∧ v = REnv.get b ρ x,
        by intro ρ₁ ρ₂ v h
           have hfv : ∀ y ∈ p.fv, ρ₁.ints y = ρ₂.ints y ∧ ρ₁.bools y = ρ₂.bools y :=
             fun y hy => h y (List.mem_append_left _ hy)
           have hx := h x (List.mem_append_right _ (List.mem_singleton.mpr rfl))
           constructor
           · rintro ⟨hp, hv⟩
             exact ⟨(p.ext hfv).mp hp, by cases b <;> simp [REnv.get, hx.1, hx.2] at * <;> exact hv⟩
           · rintro ⟨hp, hv⟩
             exact ⟨(p.ext hfv).mpr hp, by cases b <;> simp [REnv.get, hx.1, hx.2] at * <;> exact hv⟩⟩
    | _, .arrow x t1 t2 => .arrow x t1 t2

namespace STLC

/-- The narrowed refinement used for the true-branch of an ite. -/
@[reducible]
def Refinement.ite_true (r : Refinement .bool) : Refinement .bool :=
  ⟨r.fv, fun ρ v => r.pred ρ v ∧ v = true,
   fun h => ⟨fun ⟨hr, hv⟩ => ⟨(r.ext h).mp hr, hv⟩,
              fun ⟨hr, hv⟩ => ⟨(r.ext h).mpr hr, hv⟩⟩⟩

/-- The narrowed refinement used for the false-branch of an ite. -/
@[reducible]
def Refinement.ite_false (r : Refinement .bool) : Refinement .bool :=
  ⟨r.fv, fun ρ v => r.pred ρ v ∧ v = false,
   fun h => ⟨fun ⟨hr, hv⟩ => ⟨(r.ext h).mp hr, hv⟩,
              fun ⟨hr, hv⟩ => ⟨(r.ext h).mpr hr, hv⟩⟩⟩

end STLC

mutual
  -- Γ ⊢ e ⇒ t : "e synthesizes type t"
  inductive Synth : TEnv → Exp → Ty → Prop where
    /-- SYN-VAR -/
    | var {Γ x t} :
        Γ.lookup x = some t →
        Synth Γ (.var x) (self x t)

    /-- SYN-CON: integer literal gets its singleton type. -/
    | int_const {Γ n} :
        Synth Γ (.iconst n) (prim n)

    /-- SYN-BOOL: boolean literal gets its singleton type. -/
    | bool_const {Γ b} :
        Synth Γ (.bconst b) (primBool b)

    /-- SYN-ANN: an annotated term synthesizes the annotation, after checking. -/
    | ann {Γ e t} :
        Check Γ e t →
        Synth Γ (.ann e t) t

    /-- SYN-APP (ANF): function applied to a *variable* substitutes the binder. -/
    | app {Γ e₁ y x s t} :
        Synth Γ e₁ (.arrow x s t) →
        Check Γ (.var y) s        →
        Synth Γ (.app e₁ (.var y)) (t.rename x y)

    /-- SYN-LEQ (ANF): both operands must be int-bound variables. -/
    | leq_var {Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth Γ (.leq (.var x) (.var y))
          (.refine .bool ⟨[x, y], fun ρ v => v = decide (ρ.ints x ≤ ρ.ints y),
            by intro ρ₁ ρ₂ v h
               have hx : ρ₁.ints x = ρ₂.ints x := (h x (by simp)).1
               have hy : ρ₁.ints y = ρ₂.ints y := (h y (by simp)).1
               simp [hx, hy]⟩)

    /-- SYN-NOT: synthesize the inner bool expression, then negate
        (existential refinement, sound for arbitrary inner refinements). -/
    | not_ {Γ e r} :
        Synth Γ e (.refine .bool r) →
        Synth Γ (.not e)
          (.refine .bool ⟨r.fv, fun ρ v => ∃ b, r.pred ρ b ∧ v = !b,
            by intro ρ₁ ρ₂ v h
               constructor
               · rintro ⟨bv, hb, hv⟩; exact ⟨bv, (r.ext h).mp hb, hv⟩
               · rintro ⟨bv, hb, hv⟩; exact ⟨bv, (r.ext h).mpr hb, hv⟩⟩)

    /-- SYN-ADD (ANF): both operands must be int-bound variables. -/
    | add_var {Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth Γ (.add (.var x) (.var y))
          (.refine .int ⟨[x, y], fun ρ v => v = ρ.ints x + ρ.ints y,
            by intro ρ₁ ρ₂ v h
               have hx : ρ₁.ints x = ρ₂.ints x := (h x (by simp)).1
               have hy : ρ₁.ints y = ρ₂.ints y := (h y (by simp)).1
               simp [hx, hy]⟩)

    /-- SYN-AND: synthesize both bool expressions, then AND
        (existential refinement). -/
    | and_ {Γ e₁ e₂ r₁ r₂} :
        Synth Γ e₁ (.refine .bool r₁) →
        Synth Γ e₂ (.refine .bool r₂) →
        Synth Γ (.and e₁ e₂)
          (.refine .bool
            ⟨r₁.fv ++ r₂.fv, fun ρ v => ∃ b₁ b₂, r₁.pred ρ b₁ ∧ r₂.pred ρ b₂ ∧ v = (b₁ && b₂),
              by intro ρ₁ ρ₂ v h
                 have h₁ : ∀ y ∈ r₁.fv, ρ₁.ints y = ρ₂.ints y ∧ ρ₁.bools y = ρ₂.bools y :=
                   fun y hy => h y (List.mem_append_left _ hy)
                 have h₂ : ∀ y ∈ r₂.fv, ρ₁.ints y = ρ₂.ints y ∧ ρ₁.bools y = ρ₂.bools y :=
                   fun y hy => h y (List.mem_append_right _ hy)
                 constructor
                 · rintro ⟨b₁, b₂, hb₁, hb₂, hv⟩
                   exact ⟨b₁, b₂, (r₁.ext h₁).mp hb₁, (r₂.ext h₂).mp hb₂, hv⟩
                 · rintro ⟨b₁, b₂, hb₁, hb₂, hv⟩
                   exact ⟨b₁, b₂, (r₁.ext h₁).mpr hb₁, (r₂.ext h₂).mpr hb₂, hv⟩⟩)

  -- Γ ⊢ e ⇐ t : "e checks against type t"
  inductive Check : TEnv → Exp → Ty → Prop where
    /-- CHK-SYN (subsumption): the *only* rule that emits a subtyping VC. -/
    | sub {Γ e s t} :
        Synth Γ e s  →
        Subtyp Γ s t →
        Check Γ e t

    /-- CHK-LAM: check body against codomain in extended env. Requires same
        binder and no shadowing. -/
    | lam {Γ x e s₁ s₂} :
        Γ.lookup x = none →
        Check ((x, s₁) :: Γ) e s₂ →
        Check Γ (.lam x e) (.arrow x s₁ s₂)

    /-- CHK-LET: synthesize the binding, push the obligation into the body.
        Requires no shadowing. -/
    | letin {Γ x e₁ e₂ s t}:
        Γ.lookup x = none →
        Synth Γ e₁ s →
        Check ((x, s) :: Γ) e₂ t →
        Check Γ (.letin x e₁ e₂) t

    /-- CHK-ITE (ANF, path-sensitive): condition must be a bool variable in scope;
        branches are checked under the path condition x=true / x=false. -/
    | ite {Γ x e₁ e₂ r t} :
        Γ.lookup x = some (.refine .bool r) →
        Check ((x, .refine .bool r.ite_true)  :: Γ) e₁ t →
        Check ((x, .refine .bool r.ite_false) :: Γ) e₂ t →
        Check Γ (.ite (.var x) e₁ e₂) t
end
