import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Substitution
import LeanFixpoint.VCG.STLC.Typing

open STLC

/-! # VC Generation for STLC (LN + deep Formula + κ)

  Algorithmic bidirectional refinement type-checker that produces a **deep**
  (syntactic) `Constraint` — a Horn-clause-flavoured VC language with `triv`,
  `head`, `conj`, `impl`, and `all` (universal). Its semantics is given by
  `Constraint.interp κ ρ : Constraint → Prop`.

  Because constraints are now pure syntax, VC generation (`sub`/`synth`/`check`)
  does not mention `κ` at all; `κ` enters only at interpretation time
  (`Constraint.interp`, `topVC`). The user existentially quantifies the `KEnv`
  to invoke the solver (`solve_fixpoint`).

-/

/-- Deep (syntactic) verification-condition language. `all x b c` is the
    universal `∀ x:b. c`; `impl φ c` is `φ ⇒ c`; `head φ` is a leaf obligation
    `φ`; `triv` is the trivially-true constraint; `conj` is conjunction. -/
inductive Constraint where
  | triv : Constraint
  | head (φ : Formula) : Constraint
  | conj (c₁ c₂ : Constraint) : Constraint
  | impl (φ : Formula) (c : Constraint) : Constraint
  | all  (x : EVar) (b : Base) (c : Constraint) : Constraint

/-- Semantics of a deep constraint under κ-assignment `κ` and env `ρ`. Reuses
    `Formula.interp` for embedded formulas; `all` binds `x` by updating `ρ`. -/
@[simp]
def Constraint.interp (κ : KEnv) (ρ : REnv) : Constraint → Prop
  | .triv       => True
  | .head φ     => Formula.interp κ ρ φ
  | .conj c₁ c₂ => Constraint.interp κ ρ c₁ ∧ Constraint.interp κ ρ c₂
  | .impl φ c   => Formula.interp κ ρ φ → Constraint.interp κ ρ c
  | .all x b c  => ∀ v : b.interp, Constraint.interp κ (ρ.update b x v) c

/-- Lower a refinement-guarded binder into the deep language:
    `{ν:b | r}`-bound `x` becomes `∀ x:b. r[ν:=x] ⇒ c` (the `ν→x` rename is the
    base-specific `substI`/`substB nuName`). Arrow-typed bindings carry no
    refinement, so they contribute just `c`. -/
@[simp, reducible]
def implyBind (x : EVar) (t : Ty) (c : Constraint) : Constraint :=
  match t with
  | .refine .int  r => .all x .int  (.impl (r.fmla.substI nuName (.fvar .int  x)) c)
  | .refine .bool r => .all x .bool (.impl (r.fmla.substB nuName (.fvar .bool x)) c)
  | .arrow _ _      => c

/-- Bridge lemma: the deep `implyBind` lowering of a refined binding interprets
    to exactly "for all `v` satisfying `r`, the body holds at `x ↦ v`". The
    `ν→x` rename is undone by `interp_substI/B_fvar`; the freshness
    side-conditions (`x ∉ r.fmla.fv/named`, `x ≠ nuName`) hold at every call
    site since `x` is produced by `EVar.fresh`. -/
theorem Constraint.interp_implyBind (κ : KEnv) {b : Base} (r : Refinement b)
    (x : EVar) (c : Constraint) (ρ : REnv)
    (hx_fv : x ∉ r.fmla.fv) (hx_named : x ∉ r.fmla.named) (hxν : x ≠ nuName) :
    Constraint.interp κ ρ (implyBind x (.refine b r) c) ↔
      ∀ v : b.interp, Refinement.interp κ r ρ v →
        Constraint.interp κ (ρ.update b x v) c := by
  cases b with
  | int =>
    simp only [Constraint.interp]
    refine forall_congr' (fun v => ?_)
    rw [Formula.interp_substI_fvar κ r.fmla nuName x (ρ.update .int x v) hx_named]
    have hval : (ρ.update .int x v).ints x = v := by simp
    rw [hval, REnv.update_comm_int_int ρ x nuName v v hxν,
        ← Formula.interp_update_fresh_int κ r.fmla x v (ρ.update .int nuName v) hx_fv hx_named]
    simp only [Refinement.interp]
  | bool =>
    simp only [Constraint.interp]
    refine forall_congr' (fun v => ?_)
    rw [Formula.interp_substB_fvar κ r.fmla nuName x (ρ.update .bool x v) hx_named]
    have hval : (ρ.update .bool x v).bools x = v := by simp
    rw [hval, REnv.update_comm_bool_bool ρ x nuName v v hxν,
        ← Formula.interp_update_fresh_bool κ r.fmla x v (ρ.update .bool nuName v) hx_fv hx_named]
    simp only [Refinement.interp]

/-- `implyBind` bridge phrased via `Ty.fv`/`Ty.named` of the bound type, which is
    exactly what the `EVar.fresh` side-conditions at call sites provide. -/
theorem Constraint.interp_implyBind' (κ : KEnv) {b : Base} (r : Refinement b)
    (x : EVar) (c : Constraint) (ρ : REnv)
    (hx_fv : x ∉ Ty.fv (.refine b r)) (hx_named : x ∉ Ty.named (.refine b r))
    (hxν : x ≠ nuName) :
    Constraint.interp κ ρ (implyBind x (.refine b r) c) ↔
      ∀ v : b.interp, Refinement.interp κ r ρ v →
        Constraint.interp κ (ρ.update b x v) c := by
  refine Constraint.interp_implyBind κ r x c ρ ?_ ?_ hxν
  · intro h; exact hx_fv (by simp only [Ty.fv, Refinement.fv, List.mem_filter]; exact ⟨h, by simp [hxν]⟩)
  · simpa [Ty.named] using hx_named

/-- Entailment of a deep constraint under κ: it interprets to a true `Prop` in
    every model of `Γ`. The semantic analogue of `Entail` for `Constraint`. -/
abbrev CEntail (κ : KEnv) (Γ : TEnv) (c : Constraint) : Prop :=
  ∀ ρ, ModelsEnv κ ρ Γ → Constraint.interp κ ρ c

/-- Algorithmic subtyping. Returns `none` on shape mismatch. Termination
    by `Ty.skel` (preserved under `openVar`). Takes `Γ` so the fresh name
    for the arrow case is picked away from the context domain. -/
def sub (Γ : TEnv) : Ty → Ty → Option Constraint
  | .refine .int  r₁, .refine .int  r₂ =>
      -- ∀ ν:int. r₁ ⇒ r₂   (ν is `nuName`, already the refinements' bound var)
      some (.all nuName .int  (.impl r₁.fmla (.head r₂.fmla)))
  | .refine .bool r₁, .refine .bool r₂ =>
      some (.all nuName .bool (.impl r₁.fmla (.head r₂.fmla)))
  | .arrow s₁ t₁, .arrow s₂ t₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ
                            ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv
                            ++ Ty.named s₁ ++ Ty.named s₂
                            ++ Ty.named t₁ ++ Ty.named t₂ ++ [nuName])
      match sub Γ s₂ s₁, sub ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) with
      | some c₁, some c₂ =>
          some (.conj c₁ (implyBind x s₂ c₂))
      | _, _ => none
  | _, _ => none
termination_by s t => s.skel + t.skel
decreasing_by all_goals
  first
    | (simp_wf; simp only [Ty.skel, Ty.skel_openVar]; omega)
    | (simp only [Ty.skel, Ty.skel_openVar]; omega)
    | omega

mutual
  def synth (Γ : TEnv) : Exp → Option (Constraint × Ty)
    | .fvar x    => Γ.lookup x |>.map (fun t => (.triv, self x t))
    | .iconst n  => some (.triv, prim n)
    | .bconst b  => some (.triv, primBool b)
    | .ann e t =>
        match check Γ e t with
        | some c => some (c, t)
        | none   => none
    | .app e₁ (.fvar y) =>
        match synth Γ e₁ with
        | some (c, .arrow s t) =>
            -- Hygiene: `y` must not capture into `t` when we open `t.openVar 0 y`.
            if y ∈ t.fv ∨ y ∈ Ty.named t ∨ y = nuName then none
            else
              match check Γ (.fvar y) s with
              | some c' => some (.conj c c', t.openVar 0 y)
              | none    => none
        | _ => none
    | .leq (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some (.triv,
              .refine .bool ⟨.and
                (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
                      (.leqI (.fvar .int x) (.fvar .int y)))
                (.imp (.leqI (.fvar .int x) (.fvar .int y))
                      (.eqB (.fvar .bool nuName) (.const .bool true)))⟩)
        | _, _ => none
    | .add (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some (.triv,
              .refine .int ⟨.eqI (.fvar .int nuName)
                                 (.add (.fvar .int x) (.fvar .int y))⟩)
        | _, _ => none
    | .not (.fvar x) =>
        match Γ.lookup x with
        | some (.refine .bool _) =>
            some (.triv,
              .refine .bool ⟨.eqB (.fvar .bool nuName) (.not (.fvar .bool x))⟩)
        | _ => none
    | .and (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .bool _), some (.refine .bool _) =>
            some (.triv,
              .refine .bool ⟨.eqB (.fvar .bool nuName) (.and (.fvar .bool x) (.fvar .bool y))⟩)
        | _, _ => none
    | _ => none
  termination_by e => 2 * e.skel
  decreasing_by all_goals
    (first | (simp only [Exp.skel]; omega) | omega)


  def check (Γ : TEnv) : Exp → Ty → Option Constraint
    | .lam e, .arrow s₁ s₂ =>
        let x := EVar.fresh (TEnv.dom Γ ++ e.fv ++ s₁.fv ++ s₂.fv
                              ++ Ty.named s₁ ++ Ty.named s₂
                              ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
        match check ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) with
        | some c => some (implyBind x s₁ c)
        | none   => none
    | .letin e₁ e₂, t =>
        match synth Γ e₁ with
        | some (c₁, s) =>
            let x := EVar.fresh (TEnv.dom Γ ++ e₂.fv ++ s.fv ++ t.fv
                                  ++ Ty.named s ++ Ty.named t
                                  ++ TEnv.tyFv Γ ++ TEnv.tyNamed Γ ++ [nuName])
            match check ((x, s) :: Γ) (e₂.openVar 0 x) t with
            | some c₂ => some (.conj c₁ (implyBind x s c₂))
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
                  match check ((x, r_true) :: Γ) e₁ t,
                        check ((x, r_false) :: Γ) e₂ t with
                  | some c₁, some c₂ =>
                      -- `x` is already bound in `ρ`, so the branch guards are just
                      -- `x = true ⇒ c₁` / `x = false ⇒ c₂` (no re-binding needed).
                      some (.conj (.impl (.eqB (.fvar .bool x) (.const .bool true))  c₁)
                                  (.impl (.eqB (.fvar .bool x) (.const .bool false)) c₂))
                  | _, _ => none
              | _ => none
        | _ => none
    | e, t =>
        -- Catch-all (Chk-Syn): synthesize, then subtype.
        match synth Γ e with
        | some (c, s) =>
            match sub Γ s t with
            | some c' => some (.conj c c')
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
  | some c => ∀ ρ : REnv, Constraint.interp κ ρ c
  | none   => False
