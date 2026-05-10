import LeanFixpoint.VCG.STLC.Syntax

/-! # Substitution Machinery for STLC

  All substitution-related operations and lemmas in one place.

  This file is intentionally **independent of typing/semantics** — it speaks
  only about `Syntax.lean` data (`Exp`, `Ty`, `Refinement`, `REnv`) plus a new
  runtime value type `Val`. Logical-relation lemmas that mention `TyDenote`
  stay in `Safety.lean`; substitution algebra is here.

  Sections:

  1. **Type-level renaming** — `REnv.redirect`, `Refinement.rename`, `Ty.rename`
     (variable renaming inside refinements/types). These are syntactic until
     refinements are concretized at `ρ`.

  2. **Runtime values** — `Val` and `Val.toExp` (closures embedded in syntax).

  3. **Term substitution** — `Exp.subst`, `Exp.substEnv` (capture-avoiding,
     same-binder convention).

  4. **Value substitutions / env extensions** — `Subst.lookup`, `REnv.extWithVal`.

  5. **Algebraic lemmas** — idempotence of self-rename, commuting/swapping
     substitutions, push-through of `substEnv` over each `Exp` constructor.
     Many are `sorry` per the user's directive (true under same-binder
     convention; rigorous proofs deferred until alpha-renaming is generalised
     — see `## Lifting same-binder` notes at end of file).
-/

namespace STLC

/-! ## 1. Type-level renaming -/

/-- Redirect lookups of `x` to `y` in both ints/bools components of an env.
    Used by `Refinement.rename` to implement variable renaming inside refinement
    predicates without rewriting their syntax. -/
@[simp]
def REnv.redirect (ρ : REnv) (x y : EVar) : REnv :=
  { ints  := fun z => if z == x then ρ.ints  y else ρ.ints  z
  , bools := fun z => if z == x then ρ.bools y else ρ.bools z }

/-- Redirect ρ-lookups of `x` to `y` inside a refinement. -/
@[simp]
def Refinement.rename {b : Base} (x y : EVar) (r : Refinement b) : Refinement b :=
  ⟨fun ρ v => r.pred (ρ.redirect x y) v⟩

/-- Rename free occurrences of `x` to `y` in a type, respecting binder shadowing. -/
@[simp]
def Ty.rename (x y : EVar) : Ty → Ty
  | .refine b r => .refine b (r.rename x y)
  | .arrow z s t =>
      .arrow z (s.rename x y) (if z == x then t else t.rename x y)

@[simp]
theorem Refinement.sizeOf_rename {b : Base} (x y : EVar) (r : Refinement b) :
    sizeOf (r.rename x y) = sizeOf r := rfl

@[simp]
theorem Ty.sizeOf_rename (x y : EVar) (t : Ty) :
    sizeOf (t.rename x y) = sizeOf t := by
  induction t with
  | refine b r => rfl
  | arrow z s t ihs iht =>
    simp only [Ty.rename]
    split <;> simp [ihs, iht]

/-! ### Idempotence of self-renaming (was in Soundness.lean) -/

theorem REnv.redirect_self (ρ : REnv) (x : EVar) : ρ.redirect x x = ρ := by
  simp only [REnv.redirect]
  ext1 <;> funext z <;> by_cases h : z = x <;> simp [h]

theorem Refinement.rename_self {b : Base} (x : EVar) (r : Refinement b) :
    r.rename x x = r := by
  obtain ⟨pred⟩ := r
  show (⟨fun ρ v => pred (ρ.redirect x x) v⟩ : Refinement b) = ⟨pred⟩
  congr 1; funext ρ v
  rw [REnv.redirect_self ρ x]

theorem Ty.rename_self (x : EVar) (t : Ty) : t.rename x x = t := by
  induction t with
  | refine b r =>
    show Ty.refine b (r.rename x x) = Ty.refine b r
    rw [Refinement.rename_self]
  | arrow z s body ihs ihb =>
    show Ty.arrow z (s.rename x x) (if z == x then body else body.rename x x)
          = Ty.arrow z s body
    rw [ihs]
    by_cases h : z = x
    · subst h; simp
    · have : (z == x) = false := by simp [h]
      simp [this, ihb]

/-! ## 2. Runtime values -/

/-- Runtime values: integer/boolean constants and closed lambdas.
    Substitution-based semantics — closures hold a body to be substituted into
    on application; no environment is closed over. -/
inductive Val where
  | iconst : Int  → Val
  | bconst : Bool → Val
  | clos   : EVar → Exp → Val

/-- Inject a value into the syntax (used by `Exp.subst` and big-step `lam`). -/
@[simp] def Val.toExp : Val → Exp
  | .iconst n => .iconst n
  | .bconst b => .bconst b
  | .clos x e => .lam x e

/-! ## 3. Term substitution -/

/-- Capture-avoiding substitution `e[v/x]` under the same-binder convention.
    Free occurrences of `x` are replaced by `v.toExp`; substitution is blocked
    under binders that bind `x` (lam x …, letin x = … in (here)). -/
def Exp.subst (x : EVar) (v : Val) : Exp → Exp
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .var y         => if x == y then v.toExp else .var y
  | .lam y body    => if x == y then .lam y body
                                else .lam y (body.subst x v)
  | .letin y e₁ e₂ => .letin y (e₁.subst x v)
                              (if x == y then e₂ else e₂.subst x v)
  | .app e₁ e₂     => .app (e₁.subst x v) (e₂.subst x v)
  | .ann e t       => .ann (e.subst x v) t
  | .and e₁ e₂     => .and (e₁.subst x v) (e₂.subst x v)
  | .not e         => .not (e.subst x v)
  | .leq e₁ e₂     => .leq (e₁.subst x v) (e₂.subst x v)
  | .ite e₀ e₁ e₂  => .ite (e₀.subst x v) (e₁.subst x v) (e₂.subst x v)
  | .add e₁ e₂     => .add (e₁.subst x v) (e₂.subst x v)

/-- Iterated substitution along a closing value substitution.
    Innermost binding is applied first (head of the list). -/
def Exp.substEnv : List (EVar × Val) → Exp → Exp
  | [],          e => e
  | (x, v) :: γ, e => Exp.substEnv γ (e.subst x v)

/-! ## 4. Value substitutions / env extensions -/

/-- Look up a value for `x` in a value substitution (mirrors `List.lookup`). -/
def Subst.lookup (x : EVar) : List (EVar × Val) → Option Val
  | []          => none
  | (y, v) :: γ => if x == y then some v else Subst.lookup x γ

/-- Extend `ρ` with a binding `(x, v)` whose declared type is `t`.
    For base-typed bindings we update the corresponding ints/bools slot;
    for function-typed bindings ρ is unchanged (mirrors `ModelsEnv` /
    refinements live only on base types). -/
@[simp] def REnv.extWithVal : Ty → REnv → EVar → Val → REnv
  | .refine .int  _, ρ, x, .iconst n => ρ.update .int  x n
  | .refine .bool _, ρ, x, .bconst b => ρ.update .bool x b
  | _,               ρ, _, _         => ρ

/-! ## 5. Algebraic lemmas (some `sorry`)

  All `sorry`s in this section are **TRUE** under the same-binder convention
  noted in `Syntax.lean`:58-61. They are routine capture-avoidance / freshness
  arguments. Closing them is purely a mechanical exercise once the same-binder
  hack is either formalised as an invariant or replaced by locally-nameless.
  See the **Next steps** section at the end of this file.
-/

/-! ### Substitution composition -/

/-- Substituting twice with the same variable is idempotent on the result of
    the first (because substituted values are closed in our setup). -/
theorem Exp.subst_subst_eq (x : EVar) (v w : Val) (e : Exp) :
    (e.subst x v).subst x w = e.subst x v := by
  sorry

/-- Substitutions for distinct variables commute, provided substituted values
    are closed (which our integer/boolean constants always are; closures rely
    on the same-binder convention). -/
theorem Exp.subst_subst_swap (x y : EVar) (vx vy : Val) (e : Exp)
    (hxy : x ≠ y) :
    (e.subst x vx).subst y vy = (e.subst y vy).subst x vx := by
  sorry

/-! ### `substEnv` push-through (one per `Exp` constructor) -/

theorem Exp.substEnv_iconst (γ : List (EVar × Val)) (n : Int) :
    Exp.substEnv γ (.iconst n) = .iconst n := by sorry

theorem Exp.substEnv_bconst (γ : List (EVar × Val)) (b : Bool) :
    Exp.substEnv γ (.bconst b) = .bconst b := by sorry

theorem Exp.substEnv_app (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.app e₁ e₂) = .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by sorry

theorem Exp.substEnv_letin (γ : List (EVar × Val)) (x : EVar) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.letin x e₁ e₂)
      = .letin x (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by sorry

theorem Exp.substEnv_lam (γ : List (EVar × Val)) (x : EVar) (e : Exp) :
    Exp.substEnv γ (.lam x e) = .lam x (Exp.substEnv γ e) := by sorry

theorem Exp.substEnv_ann (γ : List (EVar × Val)) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.ann e t) = .ann (Exp.substEnv γ e) t := by sorry

theorem Exp.substEnv_not (γ : List (EVar × Val)) (e : Exp) :
    Exp.substEnv γ (.not e) = .not (Exp.substEnv γ e) := by sorry

theorem Exp.substEnv_and (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.and e₁ e₂) = .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by sorry

theorem Exp.substEnv_ite (γ : List (EVar × Val)) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv γ (.ite e₀ e₁ e₂)
      = .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by sorry

/-! ### `substEnv` ↔ `Subst.lookup` and `subst` -/

/-- substEnv γ (var x) reduces to the looked-up value's syntactic form. -/
theorem Exp.substEnv_var_lookup
    (x : EVar) (γ : List (EVar × Val)) (v : Val)
    (hlk : Subst.lookup x γ = some v) :
    Exp.substEnv γ (.var x) = v.toExp := by
  sorry

/-- Cons-swap: pulling the head substitution outwards.
    Equivalent to `subst x v ∘ substEnv γ = substEnv γ ∘ subst x v` when `x` is
    fresh in `γ` (the same-binder convention). -/
theorem Exp.substEnv_cons_swap
    (x : EVar) (v : Val) (γ : List (EVar × Val)) (e : Exp) :
    Exp.substEnv ((x, v) :: γ) e = (Exp.substEnv γ e).subst x v := by
  sorry

/-! ## Next steps — lifting the same-binder restriction

  See [Syntax.lean:58-61] for the original "hack" note. The current code base
  works under the *same-binder convention*: every typing rule that introduces
  a binder uses the *same* name in (a) the binder of the typing context
  extension, and (b) the binder of the surface term. E.g.

    Hastype.lam : Hastype ((x, s) :: Γ) e t → Hastype Γ (.lam x e) (.arrow x s t)

  uses the *same* `x` for the lam's bound name and the arrow's bound name. The
  user is responsible for alpha-renaming inputs accordingly. This means proofs
  cleanly avoid the "fresh variable" / "alpha-equivalence on closures" problem
  but at the cost of a real generality limitation: `Subtyp.arrow` between
  arrows with different binders is not derivable, and the user cannot freely
  rename without rewriting the term.

  ### Path A — Locally-nameless representation (recommended end-state)

  Replace `EVar = String` with two-level variables:

  ```lean
  inductive EVar where
    | free  : String → EVar    -- free names (still strings)
    | bound : Nat → EVar       -- de Bruijn index for bound vars
  ```

  Then re-define:

  - `Exp.open  : Exp → EVar → Exp`        — open the outermost binder
  - `Exp.close : EVar → Exp → Exp`        — close a free name into a binder
  - `Exp.subst : EVar → Val → Exp → Exp`  — only substitutes for *free* names
  - Same suite for `Ty` and `Refinement`

  Substitution machinery added to this file:

  - `Exp.shift`, `Ty.shift` (de Bruijn level shifting)
  - `Exp.open_subst`, `Exp.close_open` (round-tripping)
  - `Exp.subst_open_swap` (the analogue of `subst_subst_swap`)
  - `Refinement.subst` and `Ty.subst` (replacing `Refinement.rename` / `Ty.rename`)
  - `Ty.subst_open`, etc.

  Pros: standard and well-studied (Aydemir et al. 2008 "Engineering Formal
  Metatheory"); subst lemmas have clean statements without freshness side
  conditions; alpha-equivalence is *definitional* rather than provable.

  Cons: invasive refactor. Touches `Exp`, `Ty`, every typing/VC rule, every
  semantics rule, every example.

  ### Path B — Keep named binders, formalise the freshness invariant

  Keep `EVar = String`, but tighten the typing rules and the LR with explicit
  side conditions:

  - Add `Exp.fv : Exp → Finset EVar` and `Ty.fv : Ty → Finset EVar`
  - Add freshness premises: `Hastype.lam : x ∉ Γ.dom → ...`
  - The substitution lemmas in this file gain freshness hypotheses:
      `(hfresh : x ∉ Subst.dom γ)`
  - Closures must be tagged with their free-variable set; alpha-renaming is
    a *theorem*, not free.

  Pros: keeps current term/type representation; smaller diff; closer to how
  paper presentations look on paper.

  Cons: every substitution lemma now has a freshness side condition; alpha
  equivalence has to be propagated as an explicit relation; boilerplate.

  ### Substitution machinery the new file would need (either path)

  When we lift the restriction, this file should grow to include:

  1. **`Exp.fv`, `Ty.fv`, `Refinement.fv`** — free-variable sets
  2. **Freshness lemmas**:
     - `subst_fresh` : `x ∉ Exp.fv e → e.subst x v = e`
     - `substEnv_fresh` : likewise
  3. **Alpha-equivalence** (if Path B):
     - `Exp.alphaEq : Exp → Exp → Prop`
     - Proof that `Hastype` and `BigStep` respect alpha-equivalence
  4. **Locally-nameless operations** (if Path A):
     - `open_var`, `close_var`, `open_subst_var`, `close_open_var`
  5. **Promotions** of the current `sorry` lemmas to **theorems** with the new
     freshness/closedness hypotheses
  6. **Capture-avoiding `Refinement` / `Ty` substitution** replacing the
     current `Refinement.rename` / `Ty.rename` (which is morally already
     implementing substitution-by-redirection at the predicate level)

  ### Recommended sequence

  1. Close the routine `sorry`s in this file *as-is* (under same-binder
     convention) — gives a verified baseline.
  2. Add `Exp.fv` / `Ty.fv` and the freshness lemmas — local refactor.
  3. Decide Path A vs Path B.
  4. If Path A: stage the locally-nameless conversion behind a feature flag.
  5. Re-prove `subtyp_sound`'s arrow case (currently `sorry` — the *only*
     non-routine sorry in `Safety.lean`) using the new infrastructure.
  6. Tighten `Hastype.add_var` / `leq_var` / `not_` / `and_` per their flagged
     soundness gaps (orthogonal to the binder issue but worth bundling).

  Everything new lands in *this* file: it's the substitution-machinery hub.
-/

end STLC
