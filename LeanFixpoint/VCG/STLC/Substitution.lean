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

/-- Redirect ρ-lookups of `x` to `y` inside a refinement.
    The free-variable set maps every occurrence of `x` in `r.fv` to `y`.
    This gives `rename x x = id` (self-rename is identity on fv). -/
@[simp]
def Refinement.rename {b : Base} (x y : EVar) (r : Refinement b) : Refinement b :=
  { int_fv  := r.int_fv.map (fun z => if z == x then y else z),
    bool_fv := r.bool_fv.map (fun z => if z == x then y else z),
    pred    := fun ρ v => r.pred (ρ.redirect x y) v,
    ext     := fun {ρ₁ ρ₂ v} h_int h_bool =>
      r.ext
        (fun z hz => by
          show (if z == x then ρ₁.ints y else ρ₁.ints z) =
               (if z == x then ρ₂.ints y else ρ₂.ints z)
          cases h : z == x
          · simp [h]; exact h_int z (List.mem_map.mpr ⟨z, hz, by simp [h]⟩)
          · simp [h]; exact h_int y (List.mem_map.mpr ⟨z, hz, by simp [h]⟩))
        (fun z hz => by
          show (if z == x then ρ₁.bools y else ρ₁.bools z) =
               (if z == x then ρ₂.bools y else ρ₂.bools z)
          cases h : z == x
          · simp [h]; exact h_bool z (List.mem_map.mpr ⟨z, hz, by simp [h]⟩)
          · simp [h]; exact h_bool y (List.mem_map.mpr ⟨z, hz, by simp [h]⟩)) }

/-- Rename free occurrences of `x` to `y` in a type, respecting binder shadowing. -/
@[simp]
def Ty.rename (x y : EVar) : Ty → Ty
  | .refine b r => .refine b (r.rename x y)
  | .arrow z s t =>
      .arrow z (s.rename x y) (if z == x then t else t.rename x y)

/-! ### Idempotence of self-renaming (was in Soundness.lean) -/

theorem REnv.redirect_self (ρ : REnv) (x : EVar) : ρ.redirect x x = ρ := by
  simp only [REnv.redirect]
  ext1 <;> funext z <;> by_cases h : z = x <;> simp [h]

theorem Refinement.rename_self {b : Base} (x : EVar) (r : Refinement b) :
    r.rename x x = r := by
  -- Semantically true: redirect x x = id, and fv.map (if · == x then x else ·) = fv.
  -- The fv-list equality requires List.map_id on a conditional identity.
  -- The pred equality follows from REnv.redirect_self.
  -- Not needed by Safety.lean; deferred.
  sorry

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

/-- Domain (list of bound names) of a value substitution. -/
def Subst.dom : List (EVar × Val) → List EVar
  | []          => []
  | (x, _) :: γ => x :: Subst.dom γ

/-- Extend `ρ` with a binding `(x, v)` whose declared type is `t`.
    For base-typed bindings we update the corresponding ints/bools slot;
    for function-typed bindings ρ is unchanged (mirrors `ModelsEnv` /
    refinements live only on base types). -/
@[simp] def REnv.extWithVal : Ty → REnv → EVar → Val → REnv
  | .refine .int  _, ρ, x, .iconst n =>
      { ints  := fun z => if x == z then n     else ρ.ints z
      , bools := fun z => if x == z then false  else ρ.bools z }
  | .refine .bool _, ρ, x, .bconst b =>
      { ints  := fun z => if x == z then 0     else ρ.ints z
      , bools := fun z => if x == z then b     else ρ.bools z }
  | _,               ρ, _, _         => ρ

/-! ### Free variables (for stating capture-avoidance preconditions) -/

/-- Free variables of an expression. -/
@[simp] def Exp.fv : Exp → List EVar
  | .iconst _      => []
  | .bconst _      => []
  | .var x         => [x]
  | .lam y body    => body.fv.filter (fun z => z != y)
  | .letin y e₁ e₂ => e₁.fv ++ e₂.fv.filter (fun z => z != y)
  | .app e₁ e₂     => e₁.fv ++ e₂.fv
  | .ann e _       => e.fv
  | .and e₁ e₂     => e₁.fv ++ e₂.fv
  | .not e         => e.fv
  | .leq e₁ e₂     => e₁.fv ++ e₂.fv
  | .ite e₀ e₁ e₂  => e₀.fv ++ e₁.fv ++ e₂.fv
  | .add e₁ e₂     => e₁.fv ++ e₂.fv

/-- Free variables of a value (closures shadow their parameter). -/
@[simp] def Val.fv : Val → List EVar
  | .iconst _   => []
  | .bconst _   => []
  | .clos x e   => e.fv.filter (fun z => z != x)

/-- Closedness predicate on values. Convenience abbreviation. -/
@[simp] def Val.closed (v : Val) : Prop := v.fv = []

/-- Closedness pointwise on a value substitution. -/
def Subst.AllClosed : List (EVar × Val) → Prop
  | []          => True
  | (_, v) :: γ => Val.closed v ∧ Subst.AllClosed γ

/-! ## 5. Algebraic lemmas

  Most lemmas now have explicit freshness / closedness preconditions. These
  are minimal sufficient conditions to make the algebra true; under the
  same-binder convention used in `Hastype` rules, the preconditions are
  satisfied by construction (γ has unique keys, all values are closed under
  the post-substitution domain).
-/

/-! ### Cornerstone: freshness lemma

  `e.subst x v = e` whenever `x` is not free in `e`. Foundation for everything
  below. Proved by structural induction on `e`. -/

/-- Helper: convert `x ≠ y` to `(x == y) = false` for any LawfulBEq. -/
private theorem beq_false_of_ne {α : Type _} [BEq α] [LawfulBEq α] {x y : α}
    (h : x ≠ y) : (x == y) = false := by
  cases hb : x == y with
  | true  => exact absurd (LawfulBEq.eq_of_beq hb) h
  | false => rfl

theorem Exp.subst_fresh (x : EVar) (v : Val) (e : Exp) :
    x ∉ Exp.fv e → e.subst x v = e := by
  induction e with
  | iconst n => intro _; rfl
  | bconst b => intro _; rfl
  | var y =>
    intro h
    have hxy : x ≠ y := by
      intro heq; apply h; subst heq; simp [Exp.fv]
    show (if x == y then v.toExp else Exp.var y) = Exp.var y
    rw [if_neg]
    intro hbeq
    exact hxy (LawfulBEq.eq_of_beq hbeq)
  | lam y body ih =>
    intro h
    show (if x == y then Exp.lam y body else Exp.lam y (body.subst x v)) = Exp.lam y body
    by_cases hxy : x = y
    · subst hxy
      have : (x == x) = true := by simp
      rw [if_pos this]
    · have hxy' : (x == y) = false := beq_false_of_ne hxy
      rw [if_neg (by simp [hxy'])]
      congr 1
      apply ih
      intro hbody
      apply h
      simp only [Exp.fv]
      rw [List.mem_filter]
      refine ⟨hbody, ?_⟩
      simp; exact hxy
  | letin y e₁ e₂ ih₁ ih₂ =>
    intro h
    show Exp.letin y (e₁.subst x v) (if x == y then e₂ else e₂.subst x v)
       = Exp.letin y e₁ e₂
    have h₁ : x ∉ e₁.fv := by
      intro hin; apply h
      simp only [Exp.fv, List.mem_append]; left; exact hin
    rw [ih₁ h₁]
    by_cases hxy : x = y
    · subst hxy
      have : (x == x) = true := by simp
      rw [if_pos this]
    · have hxy' : (x == y) = false := beq_false_of_ne hxy
      rw [if_neg (by simp [hxy'])]
      congr 1
      apply ih₂
      intro hin
      apply h
      simp only [Exp.fv, List.mem_append]
      right
      rw [List.mem_filter]
      refine ⟨hin, ?_⟩
      simp; exact hxy
  | app e₁ e₂ ih₁ ih₂ =>
    intro h
    show Exp.app (e₁.subst x v) (e₂.subst x v) = Exp.app e₁ e₂
    have h₁ : x ∉ e₁.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; left; exact hin)
    have h₂ : x ∉ e₂.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]
  | ann e t ih =>
    intro h
    show Exp.ann (e.subst x v) t = Exp.ann e t
    have he : x ∉ e.fv := h
    rw [ih he]
  | and e₁ e₂ ih₁ ih₂ =>
    intro h
    show Exp.and (e₁.subst x v) (e₂.subst x v) = Exp.and e₁ e₂
    have h₁ : x ∉ e₁.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; left; exact hin)
    have h₂ : x ∉ e₂.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]
  | not e ih =>
    intro h
    show Exp.not (e.subst x v) = Exp.not e
    rw [ih h]
  | leq e₁ e₂ ih₁ ih₂ =>
    intro h
    show Exp.leq (e₁.subst x v) (e₂.subst x v) = Exp.leq e₁ e₂
    have h₁ : x ∉ e₁.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; left; exact hin)
    have h₂ : x ∉ e₂.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    intro h
    show Exp.ite (e₀.subst x v) (e₁.subst x v) (e₂.subst x v) = Exp.ite e₀ e₁ e₂
    -- (e₀.fv ++ e₁.fv) ++ e₂.fv : associativity matters
    have h₀ : x ∉ e₀.fv := fun hin => h (by
      simp only [Exp.fv, List.mem_append]; left; left; exact hin)
    have h₁ : x ∉ e₁.fv := fun hin => h (by
      simp only [Exp.fv, List.mem_append]; left; right; exact hin)
    have h₂ : x ∉ e₂.fv := fun hin => h (by
      simp only [Exp.fv, List.mem_append]; right; exact hin)
    rw [ih₀ h₀, ih₁ h₁, ih₂ h₂]
  | add e₁ e₂ ih₁ ih₂ =>
    intro h
    show Exp.add (e₁.subst x v) (e₂.subst x v) = Exp.add e₁ e₂
    have h₁ : x ∉ e₁.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; left; exact hin)
    have h₂ : x ∉ e₂.fv := fun hin => h (by simp only [Exp.fv, List.mem_append]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]

/-- Free variables of `v.toExp` coincide with `Val.fv v`. -/
theorem Val.fv_toExp (v : Val) : Exp.fv v.toExp = Val.fv v := by
  cases v <;> simp [Val.toExp, Exp.fv, Val.fv]

/-- substEnv leaves an expression unchanged whenever its free vars are disjoint
    from the substitution's domain. Direct induction on `γ` using `subst_fresh`. -/
theorem Exp.substEnv_fresh
    (γ : List (EVar × Val)) (e : Exp)
    (h : ∀ z ∈ Exp.fv e, z ∉ Subst.dom γ) :
    Exp.substEnv γ e = e := by
  induction γ generalizing e with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ (e.subst y w) = e
    have hy : y ∉ Exp.fv e := by
      intro hye
      have : y ∈ Subst.dom ((y, w) :: γ) := by simp [Subst.dom]
      exact h y hye this
    rw [Exp.subst_fresh y w e hy]
    apply ih
    intro z hz
    have : z ∉ Subst.dom ((y, w) :: γ) := h z hz
    simp [Subst.dom] at this
    exact this.2

/-- Closed values are stable under any substitution. -/
theorem Exp.subst_of_closed_val (x : EVar) (v w : Val) (hv : Val.closed v) :
    v.toExp.subst x w = v.toExp := by
  apply Exp.subst_fresh
  rw [Val.fv_toExp]
  intro hin
  simp only [Val.closed] at hv
  rw [hv] at hin
  simp at hin

/-- substEnv leaves a closed value's syntactic form unchanged. -/
theorem Exp.substEnv_of_closed_val (γ : List (EVar × Val)) (v : Val)
    (hv : Val.closed v) :
    Exp.substEnv γ v.toExp = v.toExp := by
  apply Exp.substEnv_fresh
  rw [Val.fv_toExp]
  intro z hz
  simp only [Val.closed] at hv
  rw [hv] at hz
  simp at hz

/-! ### `@[simp]` equation lemmas for `Exp.subst` (for use in induction proofs) -/

@[simp] theorem Exp.subst_iconst' (x : EVar) (v : Val) (n : Int) :
    (Exp.iconst n).subst x v = .iconst n := rfl
@[simp] theorem Exp.subst_bconst' (x : EVar) (v : Val) (b : Bool) :
    (Exp.bconst b).subst x v = .bconst b := rfl
@[simp] theorem Exp.subst_var' (x : EVar) (v : Val) (y : EVar) :
    (Exp.var y).subst x v = if x == y then v.toExp else .var y := rfl
@[simp] theorem Exp.subst_lam' (x : EVar) (v : Val) (y : EVar) (body : Exp) :
    (Exp.lam y body).subst x v
      = if x == y then .lam y body else .lam y (body.subst x v) := rfl
@[simp] theorem Exp.subst_letin' (x : EVar) (v : Val) (y : EVar) (e₁ e₂ : Exp) :
    (Exp.letin y e₁ e₂).subst x v
      = .letin y (e₁.subst x v) (if x == y then e₂ else e₂.subst x v) := rfl
@[simp] theorem Exp.subst_app' (x : EVar) (v : Val) (e₁ e₂ : Exp) :
    (Exp.app e₁ e₂).subst x v = .app (e₁.subst x v) (e₂.subst x v) := rfl
@[simp] theorem Exp.subst_ann' (x : EVar) (v : Val) (e : Exp) (t : Ty) :
    (Exp.ann e t).subst x v = .ann (e.subst x v) t := rfl
@[simp] theorem Exp.subst_and' (x : EVar) (v : Val) (e₁ e₂ : Exp) :
    (Exp.and e₁ e₂).subst x v = .and (e₁.subst x v) (e₂.subst x v) := rfl
@[simp] theorem Exp.subst_not' (x : EVar) (v : Val) (e : Exp) :
    (Exp.not e).subst x v = .not (e.subst x v) := rfl
@[simp] theorem Exp.subst_leq' (x : EVar) (v : Val) (e₁ e₂ : Exp) :
    (Exp.leq e₁ e₂).subst x v = .leq (e₁.subst x v) (e₂.subst x v) := rfl
@[simp] theorem Exp.subst_ite' (x : EVar) (v : Val) (e₀ e₁ e₂ : Exp) :
    (Exp.ite e₀ e₁ e₂).subst x v
      = .ite (e₀.subst x v) (e₁.subst x v) (e₂.subst x v) := rfl
@[simp] theorem Exp.subst_add' (x : EVar) (v : Val) (e₁ e₂ : Exp) :
    (Exp.add e₁ e₂).subst x v = .add (e₁.subst x v) (e₂.subst x v) := rfl

/-! ### Substitution composition -/

/-- After substituting `v` for `x` in `e`, `x` is no longer free in the result
    (provided `x` is not free in `v`). Standard "free vars shrink" lemma. -/
theorem Exp.subst_remove_var (x : EVar) (v : Val) (e : Exp) (hv : x ∉ Val.fv v) :
    x ∉ Exp.fv (e.subst x v) := by
  induction e with
  | iconst n => simp [Exp.subst, Exp.fv]
  | bconst b => simp [Exp.subst, Exp.fv]
  | var y =>
    show x ∉ (if x == y then v.toExp else Exp.var y).fv
    by_cases hxy : x = y
    · subst hxy
      have : (x == x) = true := by simp
      rw [if_pos this]
      rw [Val.fv_toExp]
      exact hv
    · have : (x == y) = false := beq_false_of_ne hxy
      rw [if_neg (by simp [this])]
      simp [Exp.fv]
      exact hxy
  | lam y body ih =>
    show x ∉ (if x == y then Exp.lam y body else Exp.lam y (body.subst x v)).fv
    by_cases hxy : x = y
    · subst hxy
      have : (x == x) = true := by simp
      rw [if_pos this]
      simp [Exp.fv, List.mem_filter]
    · have : (x == y) = false := beq_false_of_ne hxy
      rw [if_neg (by simp [this])]
      simp [Exp.fv, List.mem_filter]
      intro hin
      exact absurd hin ih
  | letin y e₁ e₂ ih₁ ih₂ =>
    show x ∉ (Exp.letin y (e₁.subst x v) (if x == y then e₂ else e₂.subst x v)).fv
    simp only [Exp.fv, List.mem_append, not_or]
    refine ⟨ih₁, ?_⟩
    by_cases hxy : x = y
    · subst hxy
      have : (x == x) = true := by simp
      rw [if_pos this]
      simp [List.mem_filter]
    · have : (x == y) = false := beq_false_of_ne hxy
      rw [if_neg (by simp [this])]
      simp [List.mem_filter]
      intro hin
      exact absurd hin ih₂
  | app e₁ e₂ ih₁ ih₂ =>
    show x ∉ (Exp.app (e₁.subst x v) (e₂.subst x v)).fv
    simp only [Exp.fv, List.mem_append, not_or]
    exact ⟨ih₁, ih₂⟩
  | ann e t ih =>
    show x ∉ (Exp.ann (e.subst x v) t).fv
    simp only [Exp.fv]; exact ih
  | and e₁ e₂ ih₁ ih₂ =>
    show x ∉ (Exp.and (e₁.subst x v) (e₂.subst x v)).fv
    simp only [Exp.fv, List.mem_append, not_or]
    exact ⟨ih₁, ih₂⟩
  | not e ih =>
    show x ∉ (Exp.not (e.subst x v)).fv
    simp only [Exp.fv]; exact ih
  | leq e₁ e₂ ih₁ ih₂ =>
    show x ∉ (Exp.leq (e₁.subst x v) (e₂.subst x v)).fv
    simp only [Exp.fv, List.mem_append, not_or]
    exact ⟨ih₁, ih₂⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    show x ∉ (Exp.ite (e₀.subst x v) (e₁.subst x v) (e₂.subst x v)).fv
    simp only [Exp.fv, List.mem_append, not_or]
    exact ⟨⟨ih₀, ih₁⟩, ih₂⟩
  | add e₁ e₂ ih₁ ih₂ =>
    show x ∉ (Exp.add (e₁.subst x v) (e₂.subst x v)).fv
    simp only [Exp.fv, List.mem_append, not_or]
    exact ⟨ih₁, ih₂⟩

/-- Substituting a closed value can only *remove* free variables from `e`;
    the result's FV is a subset of `e`'s FV. -/
theorem Exp.subst_fv_subset (x : EVar) (v : Val) (hv : Val.closed v) (e : Exp) :
    ∀ z ∈ Exp.fv (e.subst x v), z ∈ Exp.fv e := by
  have hvfv : Val.fv v = [] := hv
  induction e with
  | iconst _ => intro z hz; simp at hz
  | bconst _ => intro z hz; simp at hz
  | var y =>
    intro z hz
    by_cases hxy : x = y
    · subst hxy
      have heq : (Exp.var x).subst x v = v.toExp := by simp [Exp.subst]
      rw [heq, Val.fv_toExp, hvfv] at hz
      cases hz
    · have hb : (x == y) = false := beq_false_of_ne hxy
      have heq : (Exp.var y).subst x v = .var y := by simp [Exp.subst, hb]
      rw [heq] at hz
      exact hz
  | lam y body ih =>
    intro z hz
    by_cases hxy : x = y
    · subst hxy
      have heq : (Exp.lam x body).subst x v = .lam x body := by simp [Exp.subst]
      rw [heq] at hz; exact hz
    · have hb : (x == y) = false := beq_false_of_ne hxy
      have heq : (Exp.lam y body).subst x v = .lam y (body.subst x v) := by
        simp [Exp.subst, hb]
      rw [heq] at hz
      simp [Exp.fv, List.mem_filter] at hz ⊢
      exact ⟨ih z hz.1, hz.2⟩
  | letin y e₁ e₂ ih₁ ih₂ =>
    intro z hz
    by_cases hxy : x = y
    · subst hxy
      have heq : (Exp.letin x e₁ e₂).subst x v = .letin x (e₁.subst x v) e₂ := by
        simp [Exp.subst]
      rw [heq] at hz
      simp [Exp.fv, List.mem_append, List.mem_filter] at hz ⊢
      rcases hz with h | h
      · exact Or.inl (ih₁ z h)
      · exact Or.inr h
    · have hb : (x == y) = false := beq_false_of_ne hxy
      have heq : (Exp.letin y e₁ e₂).subst x v
               = .letin y (e₁.subst x v) (e₂.subst x v) := by simp [Exp.subst, hb]
      rw [heq] at hz
      simp [Exp.fv, List.mem_append, List.mem_filter] at hz ⊢
      rcases hz with h | ⟨h, hzy⟩
      · exact Or.inl (ih₁ z h)
      · exact Or.inr ⟨ih₂ z h, hzy⟩
  | app e₁ e₂ ih₁ ih₂ =>
    intro z hz
    have heq : (Exp.app e₁ e₂).subst x v = .app (e₁.subst x v) (e₂.subst x v) := rfl
    rw [heq] at hz
    simp [Exp.fv, List.mem_append] at hz ⊢
    rcases hz with h | h
    · exact Or.inl (ih₁ z h)
    · exact Or.inr (ih₂ z h)
  | ann e t ih =>
    intro z hz
    have heq : (Exp.ann e t).subst x v = .ann (e.subst x v) t := rfl
    rw [heq] at hz
    simp [Exp.fv] at hz ⊢
    exact ih z hz
  | and e₁ e₂ ih₁ ih₂ =>
    intro z hz
    have heq : (Exp.and e₁ e₂).subst x v = .and (e₁.subst x v) (e₂.subst x v) := rfl
    rw [heq] at hz
    simp [Exp.fv, List.mem_append] at hz ⊢
    rcases hz with h | h
    · exact Or.inl (ih₁ z h)
    · exact Or.inr (ih₂ z h)
  | not e ih =>
    intro z hz
    have heq : (Exp.not e).subst x v = .not (e.subst x v) := rfl
    rw [heq] at hz
    simp [Exp.fv] at hz ⊢
    exact ih z hz
  | leq e₁ e₂ ih₁ ih₂ =>
    intro z hz
    have heq : (Exp.leq e₁ e₂).subst x v = .leq (e₁.subst x v) (e₂.subst x v) := rfl
    rw [heq] at hz
    simp [Exp.fv, List.mem_append] at hz ⊢
    rcases hz with h | h
    · exact Or.inl (ih₁ z h)
    · exact Or.inr (ih₂ z h)
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    intro z hz
    have heq : (Exp.ite e₀ e₁ e₂).subst x v
             = .ite (e₀.subst x v) (e₁.subst x v) (e₂.subst x v) := rfl
    rw [heq] at hz
    simp [Exp.fv, List.mem_append] at hz ⊢
    rcases hz with h | h | h
    · exact Or.inl (ih₀ z h)
    · exact Or.inr (Or.inl (ih₁ z h))
    · exact Or.inr (Or.inr (ih₂ z h))
  | add e₁ e₂ ih₁ ih₂ =>
    intro z hz
    have heq : (Exp.add e₁ e₂).subst x v = .add (e₁.subst x v) (e₂.subst x v) := rfl
    rw [heq] at hz
    simp [Exp.fv, List.mem_append] at hz ⊢
    rcases hz with h | h
    · exact Or.inl (ih₁ z h)
    · exact Or.inr (ih₂ z h)

/-- Iterated version: substituting a closed `γ` can only remove FVs, and removes
    exactly the names in `Subst.dom γ`. -/
theorem Exp.substEnv_fv_subset (γ : List (EVar × Val)) (e : Exp)
    (hγ : Subst.AllClosed γ) :
    ∀ z ∈ Exp.fv (Exp.substEnv γ e), z ∈ Exp.fv e ∧ z ∉ Subst.dom γ := by
  induction γ generalizing e with
  | nil =>
    intro z hz
    refine ⟨hz, ?_⟩
    simp [Subst.dom]
  | cons head tail ih =>
    obtain ⟨y, v⟩ := head
    obtain ⟨hv, hγ'⟩ := hγ
    intro z hz
    -- substEnv ((y, v) :: tail) e = substEnv tail (e.subst y v)
    have hz_eq : Exp.substEnv ((y, v) :: tail) e = Exp.substEnv tail (e.subst y v) := rfl
    rw [hz_eq] at hz
    obtain ⟨hz_sub_fv, hz_tail⟩ := ih (e.subst y v) hγ' z hz
    refine ⟨Exp.subst_fv_subset y v hv e z hz_sub_fv, ?_⟩
    -- Need: z ∉ y :: Subst.dom tail
    have hzy : z ≠ y := by
      intro heq; subst heq
      have hv_fv : z ∉ Val.fv v := by
        rw [show Val.fv v = [] from hv]; intro h; cases h
      exact (Exp.subst_remove_var z v e hv_fv) hz_sub_fv
    simp [Subst.dom]
    exact ⟨hzy, hz_tail⟩

/-- Substituting twice with the same variable is idempotent **provided `v` is
    closed at `x`** (no new free `x` is introduced by the first substitution). -/
theorem Exp.subst_subst_eq (x : EVar) (v w : Val) (e : Exp)
    (hv : x ∉ Val.fv v) :
    (e.subst x v).subst x w = e.subst x v := by
  exact Exp.subst_fresh x w (e.subst x v) (Exp.subst_remove_var x v e hv)

/-- Substitutions for distinct variables commute, provided substituted values
    are closed at the *other* variable. Standard structural induction. -/
theorem Exp.subst_subst_swap (x y : EVar) (vx vy : Val) (e : Exp)
    (hxy : x ≠ y) (hvx : y ∉ Val.fv vx) (hvy : x ∉ Val.fv vy) :
    (e.subst x vx).subst y vy = (e.subst y vy).subst x vx := by
  induction e with
  | iconst n => rfl
  | bconst b => rfl
  | var z =>
    by_cases hxz : x = z
    · subst hxz
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hxy)
      simp [hyx]
      exact Exp.subst_fresh y vy vx.toExp (by rw [Val.fv_toExp]; exact hvx)
    · have hxz_b : (x == z) = false := beq_false_of_ne hxz
      by_cases hyz : y = z
      · subst hyz
        have hxy_b : (x == y) = false := beq_false_of_ne hxy
        simp [hxy_b]
        exact (Exp.subst_fresh x vx vy.toExp (by rw [Val.fv_toExp]; exact hvy)).symm
      · have hyz_b : (y == z) = false := beq_false_of_ne hyz
        simp [hxz_b, hyz_b]
  | lam z body ih =>
    by_cases hxz : x = z
    · subst hxz
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hxy)
      simp [hyx]
    · have hxz_b : (x == z) = false := beq_false_of_ne hxz
      by_cases hyz : y = z
      · subst hyz
        simp [hxz_b]
      · have hyz_b : (y == z) = false := beq_false_of_ne hyz
        simp [hxz_b, hyz_b, ih]
  | letin z e₁ e₂ ih₁ ih₂ =>
    by_cases hxz : x = z
    · subst hxz
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hxy)
      simp [hyx, ih₁]
    · have hxz_b : (x == z) = false := beq_false_of_ne hxz
      by_cases hyz : y = z
      · subst hyz
        simp [hxz_b, ih₁]
      · have hyz_b : (y == z) = false := beq_false_of_ne hyz
        simp [hxz_b, hyz_b, ih₁, ih₂]
  | app e₁ e₂ ih₁ ih₂  => simp [ih₁, ih₂]
  | ann e t ih         => simp [ih]
  | and e₁ e₂ ih₁ ih₂  => simp [ih₁, ih₂]
  | not e ih           => simp [ih]
  | leq e₁ e₂ ih₁ ih₂  => simp [ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp [ih₀, ih₁, ih₂]
  | add e₁ e₂ ih₁ ih₂  => simp [ih₁, ih₂]

/-! ### `substEnv` push-through (one per `Exp` constructor)

  Structural push-through over constructors that don't bind variables. Each
  proof is induction on `γ`: every step `subst y w` commutes definitionally
  with the constructor. -/

theorem Exp.substEnv_iconst (γ : List (EVar × Val)) (n : Int) :
    Exp.substEnv γ (.iconst n) = .iconst n := by
  induction γ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.iconst n).subst y w) = .iconst n
    show Exp.substEnv γ (Exp.iconst n) = .iconst n
    exact ih

theorem Exp.substEnv_bconst (γ : List (EVar × Val)) (b : Bool) :
    Exp.substEnv γ (.bconst b) = .bconst b := by
  induction γ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.bconst b).subst y w) = .bconst b
    show Exp.substEnv γ (Exp.bconst b) = .bconst b
    exact ih

theorem Exp.substEnv_app (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.app e₁ e₂) = .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.app e₁ e₂).subst y w)
      = Exp.app (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    show Exp.substEnv γ (.app (e₁.subst y w) (e₂.subst y w))
      = Exp.app (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    exact ih (e₁.subst y w) (e₂.subst y w)

theorem Exp.substEnv_ann (γ : List (EVar × Val)) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.ann e t) = .ann (Exp.substEnv γ e) t := by
  induction γ generalizing e with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.ann e t).subst y w) = Exp.ann (Exp.substEnv γ (e.subst y w)) t
    show Exp.substEnv γ (.ann (e.subst y w) t) = Exp.ann (Exp.substEnv γ (e.subst y w)) t
    exact ih (e.subst y w)

theorem Exp.substEnv_not (γ : List (EVar × Val)) (e : Exp) :
    Exp.substEnv γ (.not e) = .not (Exp.substEnv γ e) := by
  induction γ generalizing e with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.not e).subst y w) = Exp.not (Exp.substEnv γ (e.subst y w))
    show Exp.substEnv γ (.not (e.subst y w)) = Exp.not (Exp.substEnv γ (e.subst y w))
    exact ih (e.subst y w)

theorem Exp.substEnv_and (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.and e₁ e₂) = .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.and e₁ e₂).subst y w)
      = Exp.and (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    show Exp.substEnv γ (.and (e₁.subst y w) (e₂.subst y w))
      = Exp.and (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    exact ih (e₁.subst y w) (e₂.subst y w)

theorem Exp.substEnv_add (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.add e₁ e₂) = .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ (.add (e₁.subst y w) (e₂.subst y w))
      = Exp.add (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    exact ih (e₁.subst y w) (e₂.subst y w)

theorem Exp.substEnv_leq (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.leq e₁ e₂) = .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ (.leq (e₁.subst y w) (e₂.subst y w))
      = Exp.leq (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    exact ih (e₁.subst y w) (e₂.subst y w)

theorem Exp.substEnv_ite (γ : List (EVar × Val)) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv γ (.ite e₀ e₁ e₂)
      = .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₀ e₁ e₂ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.ite e₀ e₁ e₂).subst y w)
      = Exp.ite (Exp.substEnv γ (e₀.subst y w))
                (Exp.substEnv γ (e₁.subst y w))
                (Exp.substEnv γ (e₂.subst y w))
    show Exp.substEnv γ (.ite (e₀.subst y w) (e₁.subst y w) (e₂.subst y w))
      = Exp.ite (Exp.substEnv γ (e₀.subst y w))
                (Exp.substEnv γ (e₁.subst y w))
                (Exp.substEnv γ (e₂.subst y w))
    exact ih (e₀.subst y w) (e₁.subst y w) (e₂.subst y w)

/-! ### Binder-aware push-through (`lam`, `letin`)

  These need `x ∉ Subst.dom γ` because once `subst x w` reaches a binder named
  `x`, substitution stops. Under the same-binder convention used by `Hastype`,
  the precondition is satisfied by construction. -/

theorem Exp.substEnv_lam (γ : List (EVar × Val)) (x : EVar) (e : Exp)
    (hx : x ∉ Subst.dom γ) :
    Exp.substEnv γ (.lam x e) = .lam x (Exp.substEnv γ e) := by
  induction γ generalizing e with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    have hy_ne_x : y ≠ x := by
      intro heq
      apply hx
      simp [Subst.dom, ← heq]
    have hx_tail : x ∉ Subst.dom γ := by
      intro hin; apply hx; simp [Subst.dom]; right; exact hin
    show Exp.substEnv γ ((Exp.lam x e).subst y w) = Exp.lam x (Exp.substEnv γ (e.subst y w))
    have hxy : (y == x) = false := beq_false_of_ne hy_ne_x
    show Exp.substEnv γ (if y == x then Exp.lam x e else Exp.lam x (e.subst y w))
       = Exp.lam x (Exp.substEnv γ (e.subst y w))
    rw [if_neg (by simp [hxy])]
    exact ih (e.subst y w) hx_tail

theorem Exp.substEnv_letin (γ : List (EVar × Val)) (x : EVar) (e₁ e₂ : Exp)
    (hx : x ∉ Subst.dom γ) :
    Exp.substEnv γ (.letin x e₁ e₂)
      = .letin x (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    have hy_ne_x : y ≠ x := by
      intro heq; apply hx; simp [Subst.dom, ← heq]
    have hx_tail : x ∉ Subst.dom γ := by
      intro hin; apply hx; simp [Subst.dom]; right; exact hin
    have hxy : (y == x) = false := beq_false_of_ne hy_ne_x
    show Exp.substEnv γ ((Exp.letin x e₁ e₂).subst y w)
       = Exp.letin x (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    show Exp.substEnv γ (Exp.letin x (e₁.subst y w) (if y == x then e₂ else e₂.subst y w))
       = Exp.letin x (Exp.substEnv γ (e₁.subst y w)) (Exp.substEnv γ (e₂.subst y w))
    rw [if_neg (by simp [hxy])]
    exact ih (e₁.subst y w) (e₂.subst y w) hx_tail

/-! ### `substEnv` ↔ `Subst.lookup` and `subst` -/

/-- substEnv γ (var x) reduces to the looked-up value's syntactic form, provided
    the value is closed (no further substitutions disturb it). -/
theorem Exp.substEnv_var_lookup
    (x : EVar) (γ : List (EVar × Val)) (v : Val)
    (hlk : Subst.lookup x γ = some v) (hv : Val.closed v) :
    Exp.substEnv γ (.var x) = v.toExp := by
  induction γ with
  | nil => simp [Subst.lookup] at hlk
  | cons p γ ih =>
    obtain ⟨y, w⟩ := p
    show Exp.substEnv γ ((Exp.var x).subst y w) = v.toExp
    show Exp.substEnv γ (if y == x then w.toExp else Exp.var x) = v.toExp
    by_cases hyx : y = x
    · -- head match: lookup gave w (= v); show the rest of γ leaves w.toExp alone.
      subst hyx
      have hbeq : (y == y) = true := by simp
      rw [if_pos hbeq]
      simp only [Subst.lookup] at hlk
      have : (y == y) = true := by simp
      rw [this] at hlk
      simp at hlk
      -- hlk : w = v
      rw [hlk]
      exact Exp.substEnv_of_closed_val γ v hv
    · -- recurse on tail.
      have hyx_b : (y == x) = false := beq_false_of_ne hyx
      have hxy_b : (x == y) = false := beq_false_of_ne (Ne.symm hyx)
      rw [if_neg (by simp [hyx_b])]
      apply ih
      simp only [Subst.lookup] at hlk
      rw [hxy_b] at hlk
      simp at hlk
      exact hlk

/-- Cons-swap: pulling the head substitution outwards.
    `substEnv ((x, v) :: γ) e = (substEnv γ e).subst x v` when `x` is fresh in
    `γ` and all values (head + tail) are closed.

    The proof reduces to a per-step swap (`subst_subst_swap`) followed by IH. -/
theorem Exp.substEnv_cons_swap
    (x : EVar) (v : Val) (γ : List (EVar × Val)) (e : Exp)
    (hx : x ∉ Subst.dom γ) (hv : Val.closed v) (hγ : Subst.AllClosed γ) :
    Exp.substEnv ((x, v) :: γ) e = (Exp.substEnv γ e).subst x v := by
  -- After unfolding the outermost substEnv:
  -- LHS (def): substEnv γ (e.subst x v)
  -- RHS:       (substEnv γ e).subst x v
  -- Goal: those two are equal.
  show Exp.substEnv γ (e.subst x v) = (Exp.substEnv γ e).subst x v
  induction γ generalizing e with
  | nil => rfl
  | cons p γ' ih =>
    obtain ⟨y, w⟩ := p
    have hy_ne_x : y ≠ x := by
      intro heq; apply hx; simp [Subst.dom, ← heq]
    have hx_tail : x ∉ Subst.dom γ' := by
      intro hin; apply hx; simp [Subst.dom]; right; exact hin
    have ⟨hw, hγ_tail⟩ : Val.closed w ∧ Subst.AllClosed γ' := hγ
    -- Target (after def-unfolding the cons-substEnv):
    --   substEnv γ' ((e.subst x v).subst y w) = (substEnv γ' (e.subst y w)).subst x v
    show Exp.substEnv γ' ((e.subst x v).subst y w)
       = (Exp.substEnv γ' (e.subst y w)).subst x v
    -- Step 1: subst x v and subst y w commute (x ≠ y, both values closed).
    have sw : (e.subst x v).subst y w = (e.subst y w).subst x v := by
      apply Exp.subst_subst_swap x y v w e (Ne.symm hy_ne_x)
      · simp only [Val.closed] at hv
        intro hin; rw [hv] at hin; simp at hin
      · simp only [Val.closed] at hw
        intro hin; rw [hw] at hin; simp at hin
    rw [sw]
    -- Step 2: IH applied with new e := e.subst y w
    exact ih (e.subst y w) hx_tail hγ_tail

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
