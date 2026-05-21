import LeanFixpoint.VCG.STLC.Syntax

/-! # Substitution, Opening, and Interpretation (locally nameless)

  Layout:

  1. **Term** — `fv`, `openBVar`, `substI`, `substB`, `lc_at`, `interp`.
  2. **Formula** — same operations + `interp` (handles named existentials).
  3. **Refinement** — wraps Formula; ν stored as a slot of `ρ` at `nuName`.
  4. **Ty** — `fv`, `openVar` (base-tagged), `substI`, `substB`, `lc_at`.
  5. **Val** — locally-nameless closures (body has `BVar 0`).
  6. **Exp** — `fv`, `openVar`, `openExp`, `openVal`, `close`, `subst`, `lc_at`.
  7. **TEnv.fv**.
  8. **Subst + iterated value substitution** for big-step.
  9. **EVar.fresh** — produces a name not in a given list.

  This file is **definitions only**. Lemmas (subst_fresh, keystone
  interp_subst*, LN library) live below the fold but currently empty in this
  draft — they land in Stage 2b.
-/

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

/-- Substitute `u : Term .int` for free occurrences of `fvar .int x`. -/
def Term.substI {b : Base} (t : Term b) (x : EVar) (u : Term .int) : Term b :=
  match t with
  | .const b c    => .const b c
  | .bvar b j     => .bvar b j
  | .fvar .int y  => if y = x then u else .fvar .int y
  | .fvar .bool y => .fvar .bool y
  | .add t₁ t₂    => .add (t₁.substI x u) (t₂.substI x u)
  | .not t        => .not (t.substI x u)
  | .and t₁ t₂    => .and (t₁.substI x u) (t₂.substI x u)

/-- Substitute `u : Term .bool` for free occurrences of `fvar .bool x`. -/
def Term.substB {b : Base} (t : Term b) (x : EVar) (u : Term .bool) : Term b :=
  match t with
  | .const b c    => .const b c
  | .bvar b j     => .bvar b j
  | .fvar .int y  => .fvar .int y
  | .fvar .bool y => if y = x then u else .fvar .bool y
  | .add t₁ t₂    => .add (t₁.substB x u) (t₂.substB x u)
  | .not t        => .not (t.substB x u)
  | .and t₁ t₂    => .and (t₁.substB x u) (t₂.substB x u)

/-- Locally closed at level `k`: every `BVar` index is strictly less than `k`. -/
def Term.lc_at : Nat → {b : Base} → Term b → Prop
  | _, _, .const _ _   => True
  | k, _, .bvar _ j    => j < k
  | _, _, .fvar _ _    => True
  | k, _, .add t₁ t₂   => Term.lc_at k t₁ ∧ Term.lc_at k t₂
  | k, _, .not t       => Term.lc_at k t
  | k, _, .and t₁ t₂   => Term.lc_at k t₁ ∧ Term.lc_at k t₂

/-- Interpret a term in `ρ`. Free vars resolve via `REnv.get`; ν is the value
    at slot `nuName`. `BVar`s should be eliminated by opening before `interp`
    is called; on an un-opened `BVar` we return the type's default value. -/
def Term.interp (ρ : REnv) : {b : Base} → Term b → b.interp
  | _, .const _ c   => c
  | _, .bvar b _    => match b with
                       | .int  => (0 : Int)
                       | .bool => false
  | _, .fvar b x    => REnv.get b ρ x
  | _, .add t₁ t₂   => Term.interp ρ t₁ + Term.interp ρ t₂
  | _, .not t       => !Term.interp ρ t
  | _, .and t₁ t₂   => Term.interp ρ t₁ && Term.interp ρ t₂

/-! ## 2. Formula operations -/

/-- Free variables of a formula. Includes `nuName` if it appears.
    Named existentials remove their binder from the body's fv. -/
def Formula.fv : Formula → List EVar
  | .tt           => []
  | .ff           => []
  | .eqI t₁ t₂    => t₁.fv ++ t₂.fv
  | .eqB t₁ t₂    => t₁.fv ++ t₂.fv
  | .leqI t₁ t₂   => t₁.fv ++ t₂.fv
  | .and φ₁ φ₂    => Formula.fv φ₁ ++ Formula.fv φ₂
  | .or φ₁ φ₂     => Formula.fv φ₁ ++ Formula.fv φ₂
  | .not φ        => Formula.fv φ
  | .imp φ₁ φ₂    => Formula.fv φ₁ ++ Formula.fv φ₂
  | .exI x φ      => (Formula.fv φ).filter (· ≠ x)
  | .exB x φ      => (Formula.fv φ).filter (· ≠ x)
  | .allI x φ     => (Formula.fv φ).filter (· ≠ x)
  | .allB x φ     => (Formula.fv φ).filter (· ≠ x)
  | .kapp _ args  => args.flatMap (fun a => Term.fv a.2)

def Formula.named : Formula → List EVar
  | .tt           => []
  | .ff           => []
  | .eqI _ _      => []
  | .eqB _ _      => []
  | .leqI _ _     => []
  | .and φ₁ φ₂    => φ₁.named ++ φ₂.named
  | .or φ₁ φ₂     => φ₁.named ++ φ₂.named
  | .not φ        => φ.named
  | .imp φ₁ φ₂    => φ₁.named ++ φ₂.named
  | .exI x φ      => x :: φ.named
  | .exB x φ      => x :: φ.named
  | .allI x φ     => x :: φ.named
  | .allB x φ     => x :: φ.named
  | .kapp _ args  => args.flatMap (fun a => Term.fv a.2)

/-- Open the `b'`-typed `BVar` at level `k` with a free var `x` throughout `φ`. -/
def Formula.openBVar (b' : Base) (k : Nat) (x : EVar) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eqI t₁ t₂    => .eqI (t₁.openBVar b' k x) (t₂.openBVar b' k x)
  | .eqB t₁ t₂    => .eqB (t₁.openBVar b' k x) (t₂.openBVar b' k x)
  | .leqI t₁ t₂   => .leqI (t₁.openBVar b' k x) (t₂.openBVar b' k x)
  | .and φ₁ φ₂    => .and (φ₁.openBVar b' k x) (φ₂.openBVar b' k x)
  | .or φ₁ φ₂     => .or (φ₁.openBVar b' k x) (φ₂.openBVar b' k x)
  | .not φ        => .not (φ.openBVar b' k x)
  | .imp φ₁ φ₂    => .imp (φ₁.openBVar b' k x) (φ₂.openBVar b' k x)
  | .exI y φ      => .exI y (φ.openBVar b' k x)
  | .exB y φ      => .exB y (φ.openBVar b' k x)
  | .allI y φ     => .allI y (φ.openBVar b' k x)
  | .allB y φ     => .allB y (φ.openBVar b' k x)
  | .kapp kname args =>
      .kapp kname (args.map (fun a => ⟨a.1, Term.openBVar b' k x a.2⟩))

/-- Substitute `u : Term .int` for free occurrences of `fvar .int x`.
    Respects shadowing under `exI` of the same name. -/
def Formula.substI (x : EVar) (u : Term .int) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eqI t₁ t₂    => .eqI (t₁.substI x u) (t₂.substI x u)
  | .eqB t₁ t₂    => .eqB t₁ t₂           -- int-subst doesn't touch bool Terms
  | .leqI t₁ t₂   => .leqI (t₁.substI x u) (t₂.substI x u)
  | .and φ₁ φ₂    => .and (φ₁.substI x u) (φ₂.substI x u)
  | .or φ₁ φ₂     => .or (φ₁.substI x u) (φ₂.substI x u)
  | .not φ        => .not (φ.substI x u)
  | .imp φ₁ φ₂    => .imp (φ₁.substI x u) (φ₂.substI x u)
  | .exI y φ      => if x = y then .exI y φ else .exI y (φ.substI x u)
  | .exB y φ      => .exB y (φ.substI x u)  -- different base: no shadowing
  | .allI y φ     => if x = y then .allI y φ else .allI y (φ.substI x u)
  | .allB y φ     => .allB y (φ.substI x u)
  | .kapp k args  => .kapp k (args.map (fun a => ⟨a.1, a.2.substI x u⟩))

/-- Substitute `u : Term .bool` for free occurrences of `fvar .bool x`. -/
def Formula.substB (x : EVar) (u : Term .bool) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eqI t₁ t₂    => .eqI t₁ t₂
  | .eqB t₁ t₂    => .eqB (t₁.substB x u) (t₂.substB x u)
  | .leqI t₁ t₂   => .leqI t₁ t₂
  | .and φ₁ φ₂    => .and (φ₁.substB x u) (φ₂.substB x u)
  | .or φ₁ φ₂     => .or (φ₁.substB x u) (φ₂.substB x u)
  | .not φ        => .not (φ.substB x u)
  | .imp φ₁ φ₂    => .imp (φ₁.substB x u) (φ₂.substB x u)
  | .exI y φ      => .exI y (φ.substB x u)
  | .exB y φ      => if x = y then .exB y φ else .exB y (φ.substB x u)
  | .allI y φ     => .allI y (φ.substB x u)
  | .allB y φ     => if x = y then .allB y φ else .allB y (φ.substB x u)
  | .kapp k args  => .kapp k (args.map (fun a => ⟨a.1, a.2.substB x u⟩))

/-- Locally closed at level `k`: descends through formula structure. Named
    existentials don't affect `BVar` levels (they bind names, not indices). -/
def Formula.lc_at : Nat → Formula → Prop
  | _, .tt          => True
  | _, .ff          => True
  | k, .eqI t₁ t₂   => t₁.lc_at k ∧ t₂.lc_at k
  | k, .eqB t₁ t₂   => t₁.lc_at k ∧ t₂.lc_at k
  | k, .leqI t₁ t₂  => t₁.lc_at k ∧ t₂.lc_at k
  | k, .and φ₁ φ₂   => φ₁.lc_at k ∧ φ₂.lc_at k
  | k, .or φ₁ φ₂    => φ₁.lc_at k ∧ φ₂.lc_at k
  | k, .not φ       => φ.lc_at k
  | k, .imp φ₁ φ₂   => φ₁.lc_at k ∧ φ₂.lc_at k
  | k, .exI _ φ     => φ.lc_at k
  | k, .exB _ φ     => φ.lc_at k
  | k, .allI _ φ    => φ.lc_at k
  | k, .allB _ φ    => φ.lc_at k
  | k, .kapp _ args => ∀ a ∈ args, Term.lc_at k a.2

/-- Interpret a formula in `ρ` under κ-assignment `κ`. Named existentials extend
    `ρ` at the bound name. `kapp` applies the κ-symbol's interpretation to its
    `ρ`-interpreted arguments. -/
def Formula.interp (κ : KEnv) (ρ : REnv) : Formula → Prop
  | .tt           => True
  | .ff           => False
  | .eqI t₁ t₂    => Term.interp ρ t₁ = Term.interp ρ t₂
  | .eqB t₁ t₂    => Term.interp ρ t₁ = Term.interp ρ t₂
  | .leqI t₁ t₂   => Term.interp ρ t₁ ≤ Term.interp ρ t₂
  | .and φ₁ φ₂    => Formula.interp κ ρ φ₁ ∧ Formula.interp κ ρ φ₂
  | .or φ₁ φ₂     => Formula.interp κ ρ φ₁ ∨ Formula.interp κ ρ φ₂
  | .not φ        => ¬ Formula.interp κ ρ φ
  | .imp φ₁ φ₂    => Formula.interp κ ρ φ₁ → Formula.interp κ ρ φ₂
  | .exI x φ      => ∃ n : Int,  Formula.interp κ (ρ.update .int  x n) φ
  | .exB x φ      => ∃ b : Bool, Formula.interp κ (ρ.update .bool x b) φ
  | .allI x φ     => ∀ n : Int,  Formula.interp κ (ρ.update .int  x n) φ
  | .allB x φ     => ∀ b : Bool, Formula.interp κ (ρ.update .bool x b) φ
  | .kapp kname args =>
      κ kname (args.map (fun a => ⟨a.1, Term.interp ρ a.2⟩))

/-! ## 3. Refinement operations -/

/-- Free variables of a refinement: formula's fv minus `nuName` (ν is "bound"
    semantically by the refinement). -/
def Refinement.fv {b : Base} (r : Refinement b) : List EVar :=
  r.fmla.fv.filter (· ≠ nuName)

def Refinement.openBVar (b' : Base) (k : Nat) (x : EVar)
    {b : Base} (r : Refinement b) : Refinement b :=
  ⟨r.fmla.openBVar b' k x⟩

def Refinement.substI (x : EVar) (u : Term .int)
    {b : Base} (r : Refinement b) : Refinement b :=
  ⟨r.fmla.substI x u⟩

def Refinement.substB (x : EVar) (u : Term .bool)
    {b : Base} (r : Refinement b) : Refinement b :=
  ⟨r.fmla.substB x u⟩

def Refinement.lc_at (k : Nat) {b : Base} (r : Refinement b) : Prop :=
  r.fmla.lc_at k

/-- Interpret a refinement at value ν under κ-assignment: extend ρ at `nuName`
    with ν, then interpret the formula. -/
def Refinement.interp (κ : KEnv) {b : Base} (r : Refinement b)
    (ρ : REnv) (ν : b.interp) : Prop :=
  Formula.interp κ (ρ.update b nuName ν) r.fmla

/-- Denotation of a refinement at κ-assignment κ and env ρ: the predicate on
    `b.interp` defining which values satisfy it. Alias for
    `Refinement.interp κ r ρ` (point-free). -/
def Refinement.den (κ : KEnv) {b : Base} (r : Refinement b) (ρ : REnv) :
    b.interp → Prop :=
  fun ν => r.interp κ ρ ν

@[simp] theorem Refinement.den_apply (κ : KEnv) {b : Base} (r : Refinement b)
    (ρ : REnv) (ν : b.interp) : r.den κ ρ ν ↔ r.interp κ ρ ν := Iff.rfl

/-- The subtyping implication formula: `∀ ν : b. r₁(ν) → r₂(ν)`. Used by
    `Subtyp.refine` to express base-refinement subtyping as a single `Formula`. -/
def Refinement.subImp {b : Base} (r₁ r₂ : Refinement b) : Formula :=
  match b with
  | .int  => .allI nuName (.imp r₁.fmla r₂.fmla)
  | .bool => .allB nuName (.imp r₁.fmla r₂.fmla)

/-- Refinement type for an integer constant: `{ν : Int | ν = n}`. -/
@[simp] def prim (n : Int) : Ty :=
  .refine .int ⟨.eqI (.fvar .int nuName) (.const .int n)⟩

/-- Refinement type for a boolean constant: `{ν : Bool | ν = b}`. -/
@[simp] def primBool (b : Bool) : Ty :=
  .refine .bool ⟨.eqB (.fvar .bool nuName) (.const .bool b)⟩

/-- `self x t` strengthens `t` with `ν = x` (singleton refinement against the
    stored value of `x`). For function types, returns `t` unchanged. -/
@[simp] def self : EVar → Ty → Ty
  | x, .refine .int  p => .refine .int  ⟨.and p.fmla
      (.eqI (.fvar .int  nuName) (.fvar .int  x))⟩
  | x, .refine .bool p => .refine .bool ⟨.and p.fmla
      (.eqB (.fvar .bool nuName) (.fvar .bool x))⟩
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

/-- Well-formedness: all free type-level variables are bound in Γ. -/
def Ty.WF (Γ : TEnv) (t : Ty) : Prop :=
  ∀ x ∈ Ty.fv t, ∃ s, (x, s) ∈ Γ

/-- Named binders (existential/universal names) in the formulas of a type.
    Fresh names must avoid these to ensure `Formula.interp_update_fresh` applies. -/
def Ty.named : Ty → List EVar
  | .refine _ r => r.fmla.named
  | .arrow s t  => Ty.named s ++ Ty.named t

/-- Open a `Ty`'s outermost binder at level `k` with free name `x`. Replaces
    `Term.bvar b k` for both bases (at most one matches in a well-formed type). -/
def Ty.openVar (k : Nat) (x : EVar) : Ty → Ty
  | .refine b r => .refine b ((r.openBVar .int k x).openBVar .bool k x)
  | .arrow s t  => .arrow (s.openVar k x) (t.openVar (k+1) x)

/-- Base-specific opener: replaces `Term.bvar b k` only. -/
def Ty.openVarAt (k : Nat) (b : Base) (x : EVar) : Ty → Ty
  | .refine b' r => .refine b' (r.openBVar b k x)
  | .arrow s t   => .arrow (s.openVarAt k b x) (t.openVarAt (k+1) b x)

/-- Structural skeleton of `Ty`: counts arrow nesting, ignoring refinement
    bodies. Preserved by `openVar` / `openVarAt`. Used as a termination
    measure for the algorithmic subtyping function in `VCGen.lean`. -/
@[simp]
def Ty.skel : Ty → Nat
  | .refine _ _ => 0
  | .arrow s t  => 1 + s.skel + t.skel

@[simp]
theorem Ty.skel_openVar (k : Nat) (x : EVar) (t : Ty) :
    (t.openVar k x).skel = t.skel := by
  induction t generalizing k with
  | refine _ _ => rfl
  | arrow s t ihs iht => simp [Ty.openVar, Ty.skel, ihs, iht]

def Ty.substI (x : EVar) (u : Term .int) : Ty → Ty
  | .refine b r => .refine b (r.substI x u)
  | .arrow s t  => .arrow (s.substI x u) (t.substI x u)

def Ty.substB (x : EVar) (u : Term .bool) : Ty → Ty
  | .refine b r => .refine b (r.substB x u)
  | .arrow s t  => .arrow (s.substB x u) (t.substB x u)

def Ty.lc_at : Nat → Ty → Prop
  | k, .refine _ r => r.lc_at k
  | k, .arrow s t  => Ty.lc_at k s ∧ Ty.lc_at (k+1) t

abbrev Ty.lc : Ty → Prop := Ty.lc_at 0

/-! ## 5. Exp operations (locally nameless)

  (Val is declared in `Syntax.lean`; its operations follow below in §5b.) -/

def Exp.fv : Exp → List EVar
  | .bvar _        => []
  | .fvar x        => [x]
  | .iconst _      => []
  | .bconst _      => []
  | .lam body      => Exp.fv body
  | .letin e₁ e₂   => Exp.fv e₁ ++ Exp.fv e₂
  | .app e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .ann e _       => Exp.fv e
  | .and e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .not e         => Exp.fv e
  | .leq e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .ite e₀ e₁ e₂  => Exp.fv e₀ ++ Exp.fv e₁ ++ Exp.fv e₂
  | .add e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂

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

/-- Replace `bvar k` with expression `u` (capture-free if `u` is locally closed). -/
def Exp.openExp (k : Nat) (u : Exp) (e : Exp) : Exp :=
  match e with
  | .bvar j        => if j = k then u else .bvar j
  | .fvar y        => .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (Exp.openExp (k+1) u body)
  | .letin e₁ e₂   => .letin (Exp.openExp k u e₁) (Exp.openExp (k+1) u e₂)
  | .app e₁ e₂     => .app (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .ann e t       => .ann (Exp.openExp k u e) t
  | .and e₁ e₂     => .and (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .not e         => .not (Exp.openExp k u e)
  | .leq e₁ e₂     => .leq (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .ite e₀ e₁ e₂  => .ite (Exp.openExp k u e₀) (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .add e₁ e₂     => .add (Exp.openExp k u e₁) (Exp.openExp k u e₂)

/-- Close a free var `x` to `bvar k` (inverse of `openVar`). -/
def Exp.close (k : Nat) (x : EVar) : Exp → Exp
  | .bvar j        => .bvar j
  | .fvar y        => if y = x then .bvar k else .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (body.close (k+1) x)
  | .letin e₁ e₂   => .letin (e₁.close k x) (e₂.close (k+1) x)
  | .app e₁ e₂     => .app (e₁.close k x) (e₂.close k x)
  | .ann e t       => .ann (e.close k x) t
  | .and e₁ e₂     => .and (e₁.close k x) (e₂.close k x)
  | .not e         => .not (e.close k x)
  | .leq e₁ e₂     => .leq (e₁.close k x) (e₂.close k x)
  | .ite e₀ e₁ e₂  => .ite (e₀.close k x) (e₁.close k x) (e₂.close k x)
  | .add e₁ e₂     => .add (e₁.close k x) (e₂.close k x)

/-- Substitute the free var `x` with expression `u` (capture-free under LN). -/
def Exp.subst (x : EVar) (u : Exp) (e : Exp) : Exp :=
  match e with
  | .bvar j        => .bvar j
  | .fvar y        => if y = x then u else .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (Exp.subst x u body)
  | .letin e₁ e₂   => .letin (Exp.subst x u e₁) (Exp.subst x u e₂)
  | .app e₁ e₂     => .app (Exp.subst x u e₁) (Exp.subst x u e₂)
  | .ann e t       => .ann (Exp.subst x u e) t
  | .and e₁ e₂     => .and (Exp.subst x u e₁) (Exp.subst x u e₂)
  | .not e         => .not (Exp.subst x u e)
  | .leq e₁ e₂     => .leq (Exp.subst x u e₁) (Exp.subst x u e₂)
  | .ite e₀ e₁ e₂  => .ite (Exp.subst x u e₀) (Exp.subst x u e₁) (Exp.subst x u e₂)
  | .add e₁ e₂     => .add (Exp.subst x u e₁) (Exp.subst x u e₂)

/-- Locally closed at level `k`: every `bvar j` satisfies `j < k`.
    `ann`'s embedded `Ty` must be `Ty.lc_at k` as well. -/
def Exp.lc_at : Nat → Exp → Prop
  | k, .bvar j        => j < k
  | _, .fvar _        => True
  | _, .iconst _      => True
  | _, .bconst _      => True
  | k, .lam body      => body.lc_at (k+1)
  | k, .letin e₁ e₂   => e₁.lc_at k ∧ e₂.lc_at (k+1)
  | k, .app e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | k, .ann e _       => e.lc_at k
  | k, .and e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | k, .not e         => e.lc_at k
  | k, .leq e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | k, .ite e₀ e₁ e₂  => e₀.lc_at k ∧ e₁.lc_at k ∧ e₂.lc_at k
  | k, .add e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k

abbrev Exp.lc : Exp → Prop := Exp.lc_at 0

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

/-! ## 5b. Val operations (depend on Exp.* declared above) -/

def Val.fv (v : Val) : List EVar :=
  match v with
  | Val.iconst _   => []
  | Val.bconst _   => []
  | Val.clos body  => body.fv

/-- A `Val` is closed when its `toExp` is locally closed (note: the closure
    body is required `lc_at 1` since `BVar 0` is the parameter). -/
def Val.lc (v : Val) : Prop :=
  match v with
  | Val.iconst _   => True
  | Val.bconst _   => True
  | Val.clos body  => body.lc_at 1

/-- Open `bvar k` with a value (via `Val.toExp`). Handy for big-step. -/
def Exp.openVal (k : Nat) (v : Val) : Exp → Exp := Exp.openExp k v.toExp

/-! ## 7. TEnv free variables

  Free variables of a typing context = union of free vars across all types,
  excluding the bound names themselves (which are scoped left-to-right by
  the cofinite typing rules). -/
def TEnv.fv : TEnv → List EVar
  | []          => []
  | (x, t) :: Γ => t.fv ++ ((TEnv.fv Γ).filter (· ≠ x))

/-- Flat union of all type free-variables in Γ (no scoping filter). Used for
    freshness conditions: x ∉ TEnv.tyFv Γ ↔ ∀ (y,t) ∈ Γ, x ∉ t.fv. -/
def TEnv.tyFv : TEnv → List EVar
  | []          => []
  | (_, t) :: Γ => t.fv ++ TEnv.tyFv Γ

/-- Flat union of all named binders in types in Γ. -/
def TEnv.tyNamed : TEnv → List EVar
  | []          => []
  | (_, t) :: Γ => Ty.named t ++ TEnv.tyNamed Γ

theorem TEnv.not_mem_tyFv {Γ : TEnv} {x y : EVar} {t : Ty}
    (h : x ∉ TEnv.tyFv Γ) (hm : (y, t) ∈ Γ) : x ∉ t.fv := by
  induction Γ with
  | nil => simp at hm
  | cons hd tl ih =>
    obtain ⟨ky, kt⟩ := hd
    simp only [TEnv.tyFv, List.mem_append, not_or] at h
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hmtl
    · exact h.1
    · exact ih h.2 hmtl

theorem TEnv.not_mem_tyNamed {Γ : TEnv} {x y : EVar} {t : Ty}
    (h : x ∉ TEnv.tyNamed Γ) (hm : (y, t) ∈ Γ) : x ∉ Ty.named t := by
  induction Γ with
  | nil => simp at hm
  | cons hd tl ih =>
    obtain ⟨ky, kt⟩ := hd
    simp only [TEnv.tyNamed, List.mem_append, not_or] at h
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hmtl
    · exact h.1
    · exact ih h.2 hmtl

/-! ## 8. Iterated value substitution (for big-step / fundamental lemma) -/

def Subst.lookup (x : EVar) : List (EVar × Val) → Option Val
  | []          => none
  | (y, v) :: γ => if x = y then some v else Subst.lookup x γ

def Subst.dom : List (EVar × Val) → List EVar
  | []          => []
  | (x, _) :: γ => x :: Subst.dom γ

def Subst.AllClosed : List (EVar × Val) → Prop
  | []          => True
  | (_, v) :: γ => Val.lc v ∧ Subst.AllClosed γ

/-- Iterated substitution of a closing value substitution into an expression.
    Innermost binding is applied first (head of the list).

    Note: explicit positional args on `Exp.subst` — dot notation `e.subst x u`
    places `e` at `Exp.subst`'s first `Exp` position (`u`), giving the reversed
    substitution direction. -/
def Exp.substEnv : List (EVar × Val) → Exp → Exp
  | [],          e => e
  | (x, v) :: γ, e => Exp.substEnv γ (Exp.subst x v.toExp e)

/-! ## 9. Freshness helper

  `EVar.fresh L` returns a name not in `L`, by producing a string longer than
  any element of `L`. The freshness proof lives in Stage 2b. -/

def EVar.maxLen : List EVar → Nat
  | []      => 0
  | x :: xs => Nat.max x.length (EVar.maxLen xs)

def EVar.fresh (L : List EVar) : EVar :=
  String.ofList (List.replicate (EVar.maxLen L + 1) 'x')

/-! ## 10. REnv helpers -/

theorem REnv.get_update_self (b : Base) (ρ : REnv) (x : EVar) (w : b.interp) :
    REnv.get b (ρ.update b x w) x = w := by
  cases b <;> simp [REnv.get]

theorem REnv.get_update_other_key (b : Base) (ρ : REnv) (x y : EVar) (w : b.interp)
    (h : x ≠ y) :
    REnv.get b (ρ.update b x w) y = REnv.get b ρ y := by
  cases b <;> simp [REnv.get] <;>
    intro hxy <;> exact absurd hxy h

theorem REnv.get_update_int_bool (ρ : REnv) (x y : EVar) (w : Int) :
    REnv.get .bool (ρ.update .int x w) y = REnv.get .bool ρ y := by
  simp [REnv.get]

theorem REnv.get_update_bool_int (ρ : REnv) (x y : EVar) (w : Bool) :
    REnv.get .int (ρ.update .bool x w) y = REnv.get .int ρ y := by
  simp [REnv.get]

theorem REnv.update_comm_int_int (ρ : REnv) (x₁ x₂ : EVar) (w₁ w₂ : Int) (h : x₁ ≠ x₂) :
    (ρ.update .int x₁ w₁).update .int x₂ w₂
      = (ρ.update .int x₂ w₂).update .int x₁ w₁ := by
  apply REnv.ext
  · funext y
    show _ = _
    by_cases hy₁ : x₁ = y <;> by_cases hy₂ : x₂ = y
    · subst hy₁; subst hy₂; exact absurd rfl h
    · have hy₂' : (x₂ == y) = false := by simp [hy₂]
      have hy₁' : (x₁ == y) = true  := by subst hy₁; simp
      simp [hy₁', hy₂']
    · have hy₁' : (x₁ == y) = false := by simp [hy₁]
      have hy₂' : (x₂ == y) = true  := by subst hy₂; simp
      simp [hy₁', hy₂']
    · have hy₁' : (x₁ == y) = false := by simp [hy₁]
      have hy₂' : (x₂ == y) = false := by simp [hy₂]
      simp [hy₁', hy₂']
  · rfl

theorem REnv.update_comm_bool_bool (ρ : REnv) (x₁ x₂ : EVar) (w₁ w₂ : Bool) (h : x₁ ≠ x₂) :
    (ρ.update .bool x₁ w₁).update .bool x₂ w₂
      = (ρ.update .bool x₂ w₂).update .bool x₁ w₁ := by
  apply REnv.ext
  · rfl
  · funext y
    show _ = _
    by_cases hy₁ : x₁ = y <;> by_cases hy₂ : x₂ = y
    · subst hy₁; subst hy₂; exact absurd rfl h
    · have hy₂' : (x₂ == y) = false := by simp [hy₂]
      have hy₁' : (x₁ == y) = true  := by subst hy₁; simp
      simp [hy₁', hy₂']
    · have hy₁' : (x₁ == y) = false := by simp [hy₁]
      have hy₂' : (x₂ == y) = true  := by subst hy₂; simp
      simp [hy₁', hy₂']
    · have hy₁' : (x₁ == y) = false := by simp [hy₁]
      have hy₂' : (x₂ == y) = false := by simp [hy₂]
      simp [hy₁', hy₂']

theorem REnv.update_comm_int_bool (ρ : REnv) (x₁ x₂ : EVar) (w₁ : Int) (w₂ : Bool) :
    (ρ.update .int x₁ w₁).update .bool x₂ w₂
      = (ρ.update .bool x₂ w₂).update .int x₁ w₁ := by
  apply REnv.ext <;> rfl

theorem REnv.update_override_int (ρ : REnv) (x : EVar) (w₁ w₂ : Int) :
    (ρ.update .int x w₁).update .int x w₂ = ρ.update .int x w₂ := by
  apply REnv.ext
  · funext y
    show _ = _
    by_cases hy : x = y
    · have hy' : (x == y) = true := by subst hy; simp
      simp [hy']
    · have hy' : (x == y) = false := by simp [hy]
      simp [hy']
  · rfl

theorem REnv.update_override_bool (ρ : REnv) (x : EVar) (w₁ w₂ : Bool) :
    (ρ.update .bool x w₁).update .bool x w₂ = ρ.update .bool x w₂ := by
  apply REnv.ext
  · rfl
  · funext y
    show _ = _
    by_cases hy : x = y
    · have hy' : (x == y) = true := by subst hy; simp
      simp [hy']
    · have hy' : (x == y) = false := by simp [hy]
      simp [hy']

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

/-- Pair of a fresh name and its freshness proof. Usage in proofs:
    `obtain ⟨x, hx⟩ := EVar.freshWith (Γ.fv ∪ ...)`. -/
def EVar.freshWith (L : List EVar) : { x : EVar // x ∉ L } :=
  ⟨EVar.fresh L, EVar.fresh_not_mem L⟩

/-! ## 12. Term keystone lemmas -/

theorem Term.interp_substI_const {b : Base} (t : Term b)
    (x : EVar) (n : Int) (ρ : REnv) :
    Term.interp ρ (t.substI x (.const .int n)) = Term.interp (ρ.update .int x n) t := by
  induction t with
  | const b c => rfl
  | bvar bv j => cases bv <;> rfl
  | fvar bv y =>
    cases bv with
    | int =>
      simp only [Term.substI]
      by_cases hy : y = x
      · subst hy
        simp [Term.interp]
      · simp only [if_neg hy, Term.interp]
        rw [REnv.get_update_other_key .int ρ x y n (fun e => hy e.symm)]
    | bool =>
      simp only [Term.substI, Term.interp]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.substI, Term.interp]; rw [ih₁, ih₂]
  | not t ih =>
    simp only [Term.substI, Term.interp]; rw [ih]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.substI, Term.interp]; rw [ih₁, ih₂]

theorem Term.interp_substB_const {b : Base} (t : Term b)
    (x : EVar) (bv : Bool) (ρ : REnv) :
    Term.interp ρ (t.substB x (.const .bool bv)) = Term.interp (ρ.update .bool x bv) t := by
  induction t with
  | const b c => rfl
  | bvar b' j => cases b' <;> rfl
  | fvar b' y =>
    cases b' with
    | int =>
      simp only [Term.substB, Term.interp]
    | bool =>
      simp only [Term.substB]
      by_cases hy : y = x
      · subst hy
        simp [Term.interp]
      · simp only [if_neg hy, Term.interp]
        rw [REnv.get_update_other_key .bool ρ x y bv (fun e => hy e.symm)]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.substB, Term.interp]; rw [ih₁, ih₂]
  | not t ih =>
    simp only [Term.substB, Term.interp]; rw [ih]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.substB, Term.interp]; rw [ih₁, ih₂]

theorem Term.interp_update_fresh_int {b : Base} (t : Term b)
    (x : EVar) (w : Int) (ρ : REnv) (h : x ∉ t.fv) :
    Term.interp (ρ.update .int x w) t = Term.interp ρ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    have hy : x ≠ y := by
      intro he; subst he; exact h (by simp [Term.fv])
    cases bv with
    | int  =>
      simp only [Term.interp]
      exact REnv.get_update_other_key .int ρ x y w hy
    | bool =>
      simp only [Term.interp]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.interp]
    have h₁ : x ∉ t₁.fv := fun hin => h (by simp [Term.fv]; left; exact hin)
    have h₂ : x ∉ t₂.fv := fun hin => h (by simp [Term.fv]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]
  | not t ih =>
    simp only [Term.interp]; rw [ih h]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.interp]
    have h₁ : x ∉ t₁.fv := fun hin => h (by simp [Term.fv]; left; exact hin)
    have h₂ : x ∉ t₂.fv := fun hin => h (by simp [Term.fv]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]

theorem Term.interp_update_fresh_bool {b : Base} (t : Term b)
    (x : EVar) (w : Bool) (ρ : REnv) (h : x ∉ t.fv) :
    Term.interp (ρ.update .bool x w) t = Term.interp ρ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    have hy : x ≠ y := by
      intro he; subst he; exact h (by simp [Term.fv])
    cases bv with
    | int  =>
      simp only [Term.interp]
    | bool =>
      simp only [Term.interp]
      exact REnv.get_update_other_key .bool ρ x y w hy
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.interp]
    have h₁ : x ∉ t₁.fv := fun hin => h (by simp [Term.fv]; left; exact hin)
    have h₂ : x ∉ t₂.fv := fun hin => h (by simp [Term.fv]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]
  | not t ih =>
    simp only [Term.interp]; rw [ih h]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.interp]
    have h₁ : x ∉ t₁.fv := fun hin => h (by simp [Term.fv]; left; exact hin)
    have h₂ : x ∉ t₂.fv := fun hin => h (by simp [Term.fv]; right; exact hin)
    rw [ih₁ h₁, ih₂ h₂]

/-- Updating ρ at a base different from the term's base preserves interp.
    Unconditional — no freshness needed, since the bases are disjoint. -/
theorem Term.interp_update_diff_base {b b' : Base} (t : Term b)
    (x : EVar) (w : b'.interp) (h : b ≠ b') (ρ : REnv) :
    Term.interp (ρ.update b' x w) t = Term.interp ρ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    cases bv with
    | int =>
      cases b' with
      | int  => exact absurd rfl h
      | bool => rfl
    | bool =>
      cases b' with
      | int  => rfl
      | bool => exact absurd rfl h
  | add t₁ t₂ ih₁ ih₂ => simp only [Term.interp]; rw [ih₁ h, ih₂ h]
  | not t ih          => simp only [Term.interp]; rw [ih h]
  | and t₁ t₂ ih₁ ih₂ => simp only [Term.interp]; rw [ih₁ h, ih₂ h]

/-- Updating an int slot doesn't affect interp of a bool term (cross-base). -/
theorem Term.interp_update_int_of_bool (t : Term .bool)
    (x : EVar) (w : Int) (ρ : REnv) :
    Term.interp (ρ.update .int x w) t = Term.interp ρ t :=
  Term.interp_update_diff_base (b' := .int) t x w (by decide) ρ

/-- Updating a bool slot doesn't affect interp of an int term (cross-base). -/
theorem Term.interp_update_bool_of_int (t : Term .int)
    (x : EVar) (bv : Bool) (ρ : REnv) :
    Term.interp (ρ.update .bool x bv) t = Term.interp ρ t :=
  Term.interp_update_diff_base (b' := .bool) t x bv (by decide) ρ

/-! ## 13. Formula keystone lemmas

  The substitution-interp connection: substituting a constant for a free name
  is equivalent to updating ρ at that name's slot. This is the deep-embedding
  payoff — `Refinement.interp` becomes algebraic.

  We do NOT prove `Formula.interp_update_fresh` here. The hypothesis `x ∉ fv`
  is too weak for named existentials over a different base (e.g. an `exB y` with
  `x = y`): the same EVar can occur as both `.int` and `.bool`, and `Formula.fv`
  doesn't distinguish. Stage 10 will address with either a base-tagged
  `fvI`/`fvB` split or a stronger freshness premise; we don't need it for the
  app-case sorry.
-/

theorem Formula.interp_substI_const (κ : KEnv) (φ : Formula)
    (x : EVar) (n : Int) (ρ : REnv) :
    Formula.interp κ ρ (φ.substI x (.const .int n)) ↔
      Formula.interp κ (ρ.update .int x n) φ := by
  induction φ generalizing ρ with
  | tt => simp [Formula.substI, Formula.interp]
  | ff => simp [Formula.substI, Formula.interp]
  | eqI t₁ t₂ =>
    simp only [Formula.substI, Formula.interp]
    rw [Term.interp_substI_const t₁ x n ρ, Term.interp_substI_const t₂ x n ρ]
  | eqB t₁ t₂ =>
    simp only [Formula.substI, Formula.interp]
    rw [Term.interp_update_int_of_bool t₁ x n ρ,
        Term.interp_update_int_of_bool t₂ x n ρ]
  | leqI t₁ t₂ =>
    simp only [Formula.substI, Formula.interp]
    rw [Term.interp_substI_const t₁ x n ρ, Term.interp_substI_const t₂ x n ρ]
  | and φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.substI, Formula.interp]
    exact and_congr (ih₁ ρ) (ih₂ ρ)
  | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.substI, Formula.interp]
    exact or_congr (ih₁ ρ) (ih₂ ρ)
  | not φ ih =>
    simp only [Formula.substI, Formula.interp]
    exact not_congr (ih ρ)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.substI, Formula.interp]
    exact imp_congr (ih₁ ρ) (ih₂ ρ)
  | exI y φ ih =>
    simp only [Formula.substI]
    by_cases hxy : x = y
    · subst hxy
      simp only [Formula.interp]
      refine exists_congr (fun n' => ?_)
      rw [REnv.update_override_int]
    · simp only [if_neg hxy, Formula.interp]
      refine exists_congr (fun n' => ?_)
      rw [ih (ρ.update .int y n'),
          REnv.update_comm_int_int ρ y x n' n (Ne.symm hxy)]
  | exB y φ ih =>
    simp only [Formula.substI, Formula.interp]
    refine exists_congr (fun b => ?_)
    rw [ih (ρ.update .bool y b),
        (REnv.update_comm_int_bool ρ x y n b).symm]
  | allI y φ ih =>
    simp only [Formula.substI]
    by_cases hxy : x = y
    · subst hxy
      simp only [Formula.interp]
      refine forall_congr' (fun n' => ?_)
      rw [REnv.update_override_int]
    · simp only [if_neg hxy, Formula.interp]
      refine forall_congr' (fun n' => ?_)
      rw [ih (ρ.update .int y n'),
          REnv.update_comm_int_int ρ y x n' n (Ne.symm hxy)]
  | allB y φ ih =>
    simp only [Formula.substI, Formula.interp]
    refine forall_congr' (fun b => ?_)
    rw [ih (ρ.update .bool y b),
        (REnv.update_comm_int_bool ρ x y n b).symm]
  | kapp kname args =>
    show Formula.interp κ ρ (.kapp kname _) ↔
         Formula.interp κ (ρ.update .int x n) (.kapp kname args)
    simp only [Formula.interp, List.map_map]
    apply iff_of_eq
    congr 1
    apply List.map_congr_left
    intro ⟨b, t⟩ _
    show Sigma.mk b (Term.interp ρ (t.substI x (.const .int n))) =
         Sigma.mk b (Term.interp (ρ.update .int x n) t)
    rw [Term.interp_substI_const t x n ρ]

theorem Formula.interp_substB_const (κ : KEnv) (φ : Formula)
    (x : EVar) (bv : Bool) (ρ : REnv) :
    Formula.interp κ ρ (φ.substB x (.const .bool bv)) ↔
      Formula.interp κ (ρ.update .bool x bv) φ := by
  induction φ generalizing ρ with
  | tt => simp [Formula.substB, Formula.interp]
  | ff => simp [Formula.substB, Formula.interp]
  | eqI t₁ t₂ =>
    simp only [Formula.substB, Formula.interp]
    rw [Term.interp_update_bool_of_int t₁ x bv ρ,
        Term.interp_update_bool_of_int t₂ x bv ρ]
  | eqB t₁ t₂ =>
    simp only [Formula.substB, Formula.interp]
    rw [Term.interp_substB_const t₁ x bv ρ, Term.interp_substB_const t₂ x bv ρ]
  | leqI t₁ t₂ =>
    simp only [Formula.substB, Formula.interp]
    rw [Term.interp_update_bool_of_int t₁ x bv ρ,
        Term.interp_update_bool_of_int t₂ x bv ρ]
  | and φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.substB, Formula.interp]
    exact and_congr (ih₁ ρ) (ih₂ ρ)
  | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.substB, Formula.interp]
    exact or_congr (ih₁ ρ) (ih₂ ρ)
  | not φ ih =>
    simp only [Formula.substB, Formula.interp]
    exact not_congr (ih ρ)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.substB, Formula.interp]
    exact imp_congr (ih₁ ρ) (ih₂ ρ)
  | exI y φ ih =>
    simp only [Formula.substB, Formula.interp]
    refine exists_congr (fun n' => ?_)
    rw [ih (ρ.update .int y n'),
        REnv.update_comm_int_bool ρ y x n' bv]
  | exB y φ ih =>
    simp only [Formula.substB]
    by_cases hxy : x = y
    · subst hxy
      simp only [Formula.interp]
      refine exists_congr (fun b => ?_)
      rw [REnv.update_override_bool]
    · simp only [if_neg hxy, Formula.interp]
      refine exists_congr (fun b => ?_)
      rw [ih (ρ.update .bool y b),
          REnv.update_comm_bool_bool ρ y x b bv (Ne.symm hxy)]
  | allI y φ ih =>
    simp only [Formula.substB, Formula.interp]
    refine forall_congr' (fun n' => ?_)
    rw [ih (ρ.update .int y n'),
        REnv.update_comm_int_bool ρ y x n' bv]
  | allB y φ ih =>
    simp only [Formula.substB]
    by_cases hxy : x = y
    · subst hxy
      simp only [Formula.interp]
      refine forall_congr' (fun b => ?_)
      rw [REnv.update_override_bool]
    · simp only [if_neg hxy, Formula.interp]
      refine forall_congr' (fun b => ?_)
      rw [ih (ρ.update .bool y b),
          REnv.update_comm_bool_bool ρ y x b bv (Ne.symm hxy)]
  | kapp kname args =>
    show Formula.interp κ ρ (.kapp kname _) ↔
         Formula.interp κ (ρ.update .bool x bv) (.kapp kname args)
    simp only [Formula.interp, List.map_map]
    apply iff_of_eq
    congr 1
    apply List.map_congr_left
    intro ⟨b, t⟩ _
    show Sigma.mk b (Term.interp ρ (t.substB x (.const .bool bv))) =
         Sigma.mk b (Term.interp (ρ.update .bool x bv) t)
    rw [Term.interp_substB_const t x bv ρ]

/-! ## 14. Refinement keystone lemmas

  These connect syntactic substitution into a refinement (`substI`/`substB`)
  with a corresponding `ρ`-update at a non-ν name. Used by Safety.lean's T2
  app-case (the only non-routine sorry under the old design). -/

theorem Refinement.interp_substI (κ : KEnv) {b : Base} (r : Refinement b)
    (x : EVar) (n : Int) (ρ : REnv) (ν : b.interp) (hx : x ≠ nuName) :
    (r.substI x (.const .int n)).interp κ ρ ν ↔
      r.interp κ (ρ.update .int x n) ν := by
  show Formula.interp κ (ρ.update b nuName ν) (r.fmla.substI x (.const .int n))
       ↔ Formula.interp κ ((ρ.update .int x n).update b nuName ν) r.fmla
  rw [Formula.interp_substI_const]
  cases b with
  | int  => rw [REnv.update_comm_int_int ρ nuName x ν n (fun e => hx e.symm)]
  | bool => rw [(REnv.update_comm_int_bool ρ x nuName n ν).symm]

theorem Refinement.interp_substB (κ : KEnv) {b : Base} (r : Refinement b)
    (x : EVar) (bv : Bool) (ρ : REnv) (ν : b.interp) (hx : x ≠ nuName) :
    (r.substB x (.const .bool bv)).interp κ ρ ν ↔
      r.interp κ (ρ.update .bool x bv) ν := by
  show Formula.interp κ (ρ.update b nuName ν) (r.fmla.substB x (.const .bool bv))
       ↔ Formula.interp κ ((ρ.update .bool x bv).update b nuName ν) r.fmla
  rw [Formula.interp_substB_const]
  cases b with
  | int  => rw [REnv.update_comm_int_bool ρ nuName x ν bv]
  | bool => rw [REnv.update_comm_bool_bool ρ nuName x ν bv (fun e => hx e.symm)]

/-! ## 15. `Exp.substEnv` push-through lemmas

  Each says "iterated value substitution distributes over the constructor."
  All proved by induction on γ; the case for constructors that `subst` ignores
  (`iconst`, `bconst`) bottoms out trivially. -/

@[simp]
theorem Exp.substEnv_iconst (γ : List (EVar × Val)) (n : Int) :
    Exp.substEnv γ (.iconst n) = .iconst n := by
  induction γ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_bconst (γ : List (EVar × Val)) (b : Bool) :
    Exp.substEnv γ (.bconst b) = .bconst b := by
  induction γ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_bvar (γ : List (EVar × Val)) (j : Nat) :
    Exp.substEnv γ (.bvar j) = .bvar j := by
  induction γ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_lam (γ : List (EVar × Val)) (body : Exp) :
    Exp.substEnv γ (.lam body) = .lam (Exp.substEnv γ body) := by
  induction γ generalizing body with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_letin (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.letin e₁ e₂) = .letin (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_app (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.app e₁ e₂) = .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_ann (γ : List (EVar × Val)) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.ann e t) = .ann (Exp.substEnv γ e) t := by
  induction γ generalizing e with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_add (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.add e₁ e₂) = .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_leq (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.leq e₁ e₂) = .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_not (γ : List (EVar × Val)) (e : Exp) :
    Exp.substEnv γ (.not e) = .not (Exp.substEnv γ e) := by
  induction γ generalizing e with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_and (γ : List (EVar × Val)) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.and e₁ e₂) = .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₁ e₂ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

@[simp]
theorem Exp.substEnv_ite (γ : List (EVar × Val)) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv γ (.ite e₀ e₁ e₂) = .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := by
  induction γ generalizing e₀ e₁ e₂ with
  | nil => rfl
  | cons head tail ih => simp [Exp.substEnv, Exp.subst, ih]

/-- An expression with no free variables is invariant under any substitution.
    `Exp.subst x u e` substitutes `u` for `x` in `e`; when `e.fv = []`,
    there are no occurrences of `fvar x` to replace. -/
theorem Exp.subst_closed (x : EVar) (u e : Exp) (he : e.fv = []) :
    Exp.subst x u e = e := by
  induction e with
  | bvar _        => rfl
  | fvar y        => simp [Exp.fv] at he
  | iconst _      => rfl
  | bconst _      => rfl
  | lam body ih   =>
    simp [Exp.fv] at he
    show Exp.lam (Exp.subst x u body) = Exp.lam body
    rw [ih he]
  | letin e₁ e₂ ih₁ ih₂ =>
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.letin (Exp.subst x u e₁) (Exp.subst x u e₂) = Exp.letin e₁ e₂
    rw [ih₁ he.1, ih₂ he.2]
  | app e₁ e₂ ih₁ ih₂ =>
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.app (Exp.subst x u e₁) (Exp.subst x u e₂) = Exp.app e₁ e₂
    rw [ih₁ he.1, ih₂ he.2]
  | ann e t ih    =>
    simp [Exp.fv] at he
    show Exp.ann (Exp.subst x u e) t = Exp.ann e t
    rw [ih he]
  | and e₁ e₂ ih₁ ih₂ =>
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.and (Exp.subst x u e₁) (Exp.subst x u e₂) = Exp.and e₁ e₂
    rw [ih₁ he.1, ih₂ he.2]
  | not e ih      =>
    simp [Exp.fv] at he
    show Exp.not (Exp.subst x u e) = Exp.not e
    rw [ih he]
  | leq e₁ e₂ ih₁ ih₂ =>
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.leq (Exp.subst x u e₁) (Exp.subst x u e₂) = Exp.leq e₁ e₂
    rw [ih₁ he.1, ih₂ he.2]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.ite (Exp.subst x u e₀) (Exp.subst x u e₁) (Exp.subst x u e₂) = Exp.ite e₀ e₁ e₂
    rw [ih₀ he.1, ih₁ he.2.1, ih₂ he.2.2]
  | add e₁ e₂ ih₁ ih₂ =>
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.add (Exp.subst x u e₁) (Exp.subst x u e₂) = Exp.add e₁ e₂
    rw [ih₁ he.1, ih₂ he.2]

/-- A closed expression is fixed under iterated value substitution. -/
theorem Exp.substEnv_closed (γ : List (EVar × Val)) (e : Exp) (he : e.fv = []) :
    Exp.substEnv γ e = e := by
  induction γ generalizing e with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨y, w⟩ := head
    show Exp.substEnv tail (Exp.subst y w.toExp e) = e
    rw [Exp.subst_closed y w.toExp e he]
    exact ih e he

/-- A value is *closed* when it has no free names. For `iconst`/`bconst` this
    is automatic; for `clos body` it says the body's free names are all bound
    by the parameter. Separate from `Val.lc` (which constrains de Bruijn
    indices, not free names). -/
@[simp]
def Val.closed (v : Val) : Prop := Val.fv v = []

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

/-- All values in `γ` are pointwise closed. -/
def Subst.AllVClosed : List (EVar × Val) → Prop
  | []          => True
  | (_, v) :: γ => Val.closed v ∧ Subst.AllVClosed γ

/-- Substituting a closed expression for x removes x from fv and leaves others. -/
private theorem Exp.subst_fv_subset (x : EVar) (u e : Exp) (hu : u.fv = []) :
    ∀ z ∈ (Exp.subst x u e).fv, z ≠ x ∧ z ∈ e.fv := by
  induction e with
  | bvar _ | iconst _ | bconst _ => simp [Exp.fv, Exp.subst]
  | fvar y =>
    simp only [Exp.subst, Exp.fv, List.mem_singleton]
    by_cases h : y = x
    · subst h; simp [hu]
    · simp only [h, ↓reduceIte, Exp.fv, List.mem_singleton]
      intro z hz; subst hz; exact ⟨h, rfl⟩
  | lam body ih | not body ih | ann body _ ih =>
    simp only [Exp.fv, Exp.subst]; exact ih
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂
  | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, Exp.subst, List.mem_append]
    intro z hz
    rcases hz with h | h
    · obtain ⟨hne, hm⟩ := ih₁ z h; exact ⟨hne, Or.inl hm⟩
    · obtain ⟨hne, hm⟩ := ih₂ z h; exact ⟨hne, Or.inr hm⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, Exp.subst, List.mem_append]
    intro z hz
    rcases hz with (h | h) | h
    · obtain ⟨hne, hm⟩ := ih₀ z h; exact ⟨hne, Or.inl (Or.inl hm)⟩
    · obtain ⟨hne, hm⟩ := ih₁ z h; exact ⟨hne, Or.inl (Or.inr hm)⟩
    · obtain ⟨hne, hm⟩ := ih₂ z h; exact ⟨hne, Or.inr hm⟩

/-- If all free vars of e are in dom γ and γ's values are closed, substEnv e has no free vars. -/
theorem Exp.substEnv_fv_nil (γ : List (EVar × Val)) (e : Exp)
    (hcl : Subst.AllVClosed γ)
    (hfv : ∀ z ∈ e.fv, z ∈ Subst.dom γ) :
    (Exp.substEnv γ e).fv = [] := by
  induction γ generalizing e with
  | nil =>
    simp only [Exp.substEnv, Subst.dom] at *
    exact List.eq_nil_iff_forall_not_mem.mpr (fun z hz => absurd hz (by simpa using hfv z hz))
  | cons head tail ih =>
    obtain ⟨x, va⟩ := head
    obtain ⟨hva_cl, htl_cl⟩ := hcl
    simp only [Exp.substEnv]
    refine ih (Exp.subst x va.toExp e) htl_cl ?_
    intro z hz
    obtain ⟨hne, hm⟩ := Exp.subst_fv_subset x va.toExp e
      (Val.toExp_closed_of_closed hva_cl) z hz
    have hdom := hfv z hm
    simp only [Subst.dom, List.mem_cons] at hdom
    rcases hdom with rfl | h
    · exact absurd rfl hne
    · simpa [Subst.dom] using h

/-- If `x` looks up to a closed value `v` in `γ`, then iterated substitution
    of `γ` into `.fvar x` returns `v.toExp`. -/
theorem Exp.substEnv_var_lookup
    (x : EVar) (γ : List (EVar × Val)) (v : Val)
    (hlk : Subst.lookup x γ = some v) (_ : Val.closed v)
    (hγ : Subst.AllVClosed γ) :
    Exp.substEnv γ (.fvar x) = v.toExp := by
  induction γ with
  | nil => simp [Subst.lookup] at hlk
  | cons head tail ih =>
    obtain ⟨y, w⟩ := head
    obtain ⟨hwcl, hγ'⟩ := hγ
    show Exp.substEnv tail (Exp.subst y w.toExp (.fvar x)) = v.toExp
    by_cases hxy : x = y
    · -- Same key: w = v, and the substitution returns w.toExp.
      have hwv : v = w := by
        simp only [Subst.lookup, hxy, if_true] at hlk
        exact (Option.some.inj hlk).symm
      have hsub : Exp.subst y w.toExp (.fvar x) = w.toExp := by
        show (if x = y then w.toExp else .fvar x) = w.toExp
        exact if_pos hxy
      rw [hsub, hwv]
      exact Exp.substEnv_closed tail w.toExp (Val.toExp_closed_of_closed hwcl)
    · -- Different key: substitution leaves `.fvar x` unchanged; recurse.
      have hlk' : Subst.lookup x tail = some v := by
        simp only [Subst.lookup, hxy, if_false] at hlk
        exact hlk
      have hsub : Exp.subst y w.toExp (.fvar x) = .fvar x := by
        show (if x = y then w.toExp else .fvar x) = .fvar x
        exact if_neg hxy
      rw [hsub]
      exact ih hlk' hγ'

/-! ## 16. REnv update idempotence -/

theorem REnv.update_idem_int (ρ : REnv) (x : EVar) (n : Int) (h : ρ.ints x = n) :
    ρ.update .int x n = ρ := by
  apply REnv.ext
  · funext y
    simp only
    by_cases hxy : x = y
    · subst hxy; simp; exact h.symm
    · simp [hxy]
  · rfl

theorem REnv.update_idem_bool (ρ : REnv) (x : EVar) (b : Bool) (h : ρ.bools x = b) :
    ρ.update .bool x b = ρ := by
  apply REnv.ext
  · rfl
  · funext y
    simp only
    by_cases hxy : x = y
    · subst hxy; simp; exact h.symm
    · simp [hxy]

/-! ## 17. Exp.subst_openVar (standard LN lemma) -/

private theorem fv_not_mem_append_left {x : EVar} {l₁ l₂ : List EVar}
    (h : x ∉ l₁ ++ l₂) : x ∉ l₁ :=
  fun hm => h (List.mem_append_left l₂ hm)

private theorem fv_not_mem_append_right {x : EVar} {l₁ l₂ : List EVar}
    (h : x ∉ l₁ ++ l₂) : x ∉ l₂ :=
  fun hm => h (List.mem_append_right l₁ hm)

/-- Substituting the freshly-opened name back recovers `openExp`. -/
theorem Exp.subst_openVar (e : Exp) (k : Nat) (x : EVar) (u : Exp)
    (hfv : x ∉ e.fv) :
    Exp.subst x u (e.openVar k x) = Exp.openExp k u e := by
  induction e generalizing k with
  | bvar j =>
    simp [openVar]
    by_cases h : j = k
      <;> simp_all [Exp.subst, openExp]
  | fvar y =>
    have hxy : x ≠ y := fun h => hfv (by subst h; simp [Exp.fv])
    show Exp.subst x u (Exp.fvar y) = Exp.fvar y
    simp [Exp.subst]
    intro h
    simp_all
  | iconst n =>
    show Exp.subst x u (Exp.iconst n) = Exp.iconst n
    simp [Exp.subst]
  | bconst b =>
    show Exp.subst x u (Exp.bconst b) = Exp.bconst b
    simp [Exp.subst]
  | lam body ih =>
    show Exp.lam (Exp.subst x u (body.openVar (k+1) x)) = Exp.lam (Exp.openExp (k + 1) u body)
    congr 1; apply ih (k+1)
    exact fun h => hfv (by simp [Exp.fv]; exact h)
  | letin e₁ e₂ ih₁ ih₂ =>
    show Exp.letin (Exp.subst x u (e₁.openVar k x)) (Exp.subst x u (e₂.openVar (k + 1) x)) =
      Exp.letin (Exp.openExp k u e₁) (Exp.openExp (k + 1) u e₂)
    congr 1
    · exact ih₁ k (fv_not_mem_append_left (by simpa [Exp.fv] using hfv))
    · exact ih₂ (k+1) (fv_not_mem_append_right (by simpa [Exp.fv] using hfv))
  | app e₁ e₂ ih₁ ih₂ =>
    show Exp.app (Exp.subst x u (e₁.openVar k x)) (Exp.subst x u (e₂.openVar k x)) =
      Exp.app (Exp.openExp k u e₁) (Exp.openExp k u e₂)
    congr 1
    · exact ih₁ k (fv_not_mem_append_left (by simpa [Exp.fv] using hfv))
    · exact ih₂ k (fv_not_mem_append_right (by simpa [Exp.fv] using hfv))
  | ann e t ih =>
    show Exp.ann (Exp.subst x u (e.openVar k x)) t = Exp.ann (Exp.openExp k u e) t
    congr 1
    exact ih k (by simpa [Exp.fv] using hfv)
  | and e₁ e₂ ih₁ ih₂ =>
    show Exp.and (Exp.subst x u (e₁.openVar k x)) (Exp.subst x u (e₂.openVar k x)) =
      Exp.and (Exp.openExp k u e₁) (Exp.openExp k u e₂)
    congr 1
    · exact ih₁ k (fv_not_mem_append_left (by simpa [Exp.fv] using hfv))
    · exact ih₂ k (fv_not_mem_append_right (by simpa [Exp.fv] using hfv))
  | not e ih =>
    show Exp.not (Exp.subst x u (e.openVar k x)) = Exp.not (Exp.openExp k u e)
    congr 1; exact ih k (by simpa [Exp.fv] using hfv)
  | leq e₁ e₂ ih₁ ih₂ =>
    show Exp.leq (Exp.subst x u (e₁.openVar k x)) (Exp.subst x u (e₂.openVar k x)) =
      Exp.leq (Exp.openExp k u e₁) (Exp.openExp k u e₂)
    congr 1
    · exact ih₁ k (fv_not_mem_append_left (by simpa [Exp.fv] using hfv))
    · exact ih₂ k (fv_not_mem_append_right (by simpa [Exp.fv] using hfv))
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    show Exp.ite (Exp.subst x u (e₀.openVar k x)) (Exp.subst x u (e₁.openVar k x)) (Exp.subst x u (e₂.openVar k x)) =
      Exp.ite (u.openExp k e₀) (u.openExp k e₁) (u.openExp k e₂)
    simp only [Exp.fv, List.mem_append] at hfv; simp at hfv
    obtain ⟨⟨hfv₀, hfv₁⟩, hfv₂⟩ := hfv
    grind
  | add e₁ e₂ ih₁ ih₂ =>
    show Exp.add (u.subst x (e₁.openVar k x)) (u.subst x (e₂.openVar k x)) =
      Exp.add (u.openExp k e₁) (u.openExp k e₂)
    congr 1
    · exact ih₁ k (fv_not_mem_append_left (by simpa [Exp.fv] using hfv))
    · exact ih₂ k (fv_not_mem_append_right (by simpa [Exp.fv] using hfv))

/-! ## 17b. openVar of lc_at is identity -/

/-- If e has no BVar at index k (lc_at k), then openVar k y is identity. -/
theorem Exp.openVar_of_lc_at (e : Exp) (k : Nat) (y : EVar) (h : Exp.lc_at k e) :
    Exp.openVar k y e = e := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]
    have hne : j ≠ k := Nat.ne_of_lt h
    simp [hne]
  | fvar _ => rfl
  | iconst _ => rfl
  | bconst _ => rfl
  | lam body ih =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih (k+1) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1
    · exact ih₁ k h.1
    · exact ih₂ (k+1) h.2
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih₁ k h.1; exact ih₂ k h.2
  | ann e t ih =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih₁ k h.1; exact ih₂ k h.2
  | not e ih =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih₁ k h.1; exact ih₂ k h.2
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]
    rw [ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openVar]; congr 1; exact ih₁ k h.1; exact ih₂ k h.2

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

theorem Term.lc_at_mono {b : Base} (t : Term b) {j k : Nat} (hjk : j ≤ k) (h : Term.lc_at j t) :
  Term.lc_at k t := by
  induction t generalizing j k with
  | const b v => simp_all [lc_at]
  | bvar b n  => simp_all [lc_at] ; grind
  | fvar b x  => simp_all [lc_at]
  | add t₁ t₂ ih1 ih2 | and t₁ t₂ ih1 ih2 =>
    simp_all [lc_at]
    grind
  | not t ih =>
    simp_all [lc_at]
    grind

theorem Formula.lc_at_mono (φ : Formula) {j k : Nat} (hjk : j ≤ k) (h : Formula.lc_at j φ) :
  Formula.lc_at k φ := by
  induction φ generalizing j k with
  | tt => simp_all [lc_at]
  | ff => simp_all [lc_at]
  | eqI t1 t2 | eqB t1 t2 =>
    simp_all [lc_at] ; and_intros
    exact Term.lc_at_mono t1 hjk h.1
    exact Term.lc_at_mono t2 hjk h.2
  | leqI i1 i2 =>
    simp_all [lc_at] ; and_intros
    exact Term.lc_at_mono i1 hjk h.1
    exact Term.lc_at_mono i2 hjk h.2
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp_all [lc_at]
    grind
  | not φ ih =>
    simp_all [lc_at]
    grind
  | exI x φ ih | exB x φ ih | allI x φ ih | allB x φ ih =>
    simp_all [lc_at]
    grind
  | kapp x args =>
    simp_all [lc_at]
    intro a hae
    exact Term.lc_at_mono a.snd hjk (h a hae)


theorem Ty.lc_at_mono (t : Ty) {j k : Nat} (hjk : j ≤ k) (h : Ty.lc_at j t) :
  Ty.lc_at k t := by
  induction t generalizing j k with
  | refine b r =>
    simp [lc_at, Refinement.lc_at] at *
    exact Formula.lc_at_mono r.fmla hjk h
  | arrow s t ih1 ih2 =>
    grind [Formula.lc_at_mono, Refinement.lc_at, lc_at]

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

theorem Exp.subst_lc_at (y : EVar) (u e : Exp) (k : Nat)
    (hlc_e : e.lc_at k) (hlc_u : u.lc_at 0) :
    (Exp.subst y u e).lc_at k := by
  induction e generalizing k with
  | bvar j      =>
    simp_all [Exp.subst, Exp.lc_at]
  | fvar x      =>
    by_cases x = y <;> simp_all [Exp.subst, Exp.lc_at]
    apply Exp.lc_at_mono u (by omega) hlc_u
  | iconst _    => simp [Exp.subst, Exp.lc_at]
  | bconst _    => simp [Exp.subst, Exp.lc_at]
  | lam _ ih    => simp_all [Exp.subst, Exp.lc_at]
  | letin _ _ ih₁ ih₂ =>
    simp_all [Exp.subst, Exp.lc_at]
  | app _ _ ih₁ ih₂ =>
    simp_all [Exp.subst, Exp.lc_at]
  | ann _ _ ih  =>
    simp_all [Exp.subst, Exp.lc_at]
  | and _ _ ih₁ ih₂ =>
    simp_all [Exp.subst, Exp.lc_at]
  | not _ ih    =>
    simp_all [Exp.subst, Exp.lc_at]
  | leq _ _ ih₁ ih₂ =>
    simp_all [Exp.subst, Exp.lc_at]
  | ite _ _ _ ih₀ ih₁ ih₂ =>
    simp_all [Exp.subst, Exp.lc_at]
  | add _ _ ih₁ ih₂ =>
    simp_all [Exp.subst, Exp.lc_at]

theorem Exp.substEnv_lc_at (γ : List (EVar × Val)) (e : Exp) (k : Nat)
    (hγ : Subst.AllClosed γ) (hlc_e : e.lc_at k) :
    (e.substEnv γ).lc_at k := by
  induction γ generalizing e with
  | nil => simpa [Exp.substEnv]
  | cons head tail ih =>
    obtain ⟨x, v⟩ := head
    obtain ⟨hlc_v, hγ'⟩ := hγ
    simp only [Exp.substEnv]
    exact ih (subst x v.toExp e) hγ' (Exp.subst_lc_at x v.toExp e k hlc_e (Val.toExp_lc_at_zero hlc_v) )

/-! ## 18. substEnv-openVar commutation -/

/-- Subst and openVar commute when the variable names differ and u is lc. -/
theorem Exp.subst_openVar_comm (e : Exp) (k : Nat) (x y : EVar) (u : Exp)
    (hxy : x ≠ y) (hlc : Exp.lc_at 0 u) :
    Exp.subst x u (e.openVar k y) = (Exp.subst x u e).openVar k y := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar]
    by_cases hjk : j = k <;> simp_all [Exp.subst, hxy.symm, openVar]
  | fvar z =>
    by_cases h : z = x
    · subst h
      simp only [Exp.openVar, Exp.subst, if_true]
      -- u.openVar k y = u since lc_at k u (from lc_at 0 u)
      have hlck : Exp.lc_at k u := Exp.lc_at_mono u (Nat.zero_le k) hlc
      exact (Exp.openVar_of_lc_at u k y hlck).symm
    · simp only [Exp.openVar, Exp.subst, if_neg h]
  | iconst _ => rfl
  | bconst _ => rfl
  | lam body ih =>
    simp only [Exp.openVar, Exp.subst]; rw [ih (k+1)]
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.subst]; rw [ih₁ k, ih₂ (k+1)]
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.subst]; rw [ih₁ k, ih₂ k]
  | ann e t ih =>
    simp only [Exp.openVar, Exp.subst]; rw [ih k]
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.subst]; rw [ih₁ k, ih₂ k]
  | not e ih =>
    simp only [Exp.openVar, Exp.subst]; rw [ih k]
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.subst]; rw [ih₁ k, ih₂ k]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.subst]; rw [ih₀ k, ih₁ k, ih₂ k]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.subst]; rw [ih₁ k, ih₂ k]

/-- substEnv commutes with openVar when z is not in dom(γ). -/
theorem Exp.substEnv_openVar_comm (e : Exp) (k : Nat) (z : EVar)
    (γ : List (EVar × Val))
    (hz : z ∉ Subst.dom γ) (hγ : Subst.AllClosed γ) :
    Exp.substEnv γ (e.openVar k z) = (Exp.substEnv γ e).openVar k z := by
  induction γ generalizing e with
  | nil => simp [Exp.substEnv]
  | cons head tail ih =>
    obtain ⟨y, va⟩ := head
    obtain ⟨hvcl, hγ'⟩ := hγ
    simp only [Subst.dom, List.mem_cons, not_or] at hz
    obtain ⟨hyz, hz'⟩ := hz
    simp only [Exp.substEnv]
    rw [← ih (Exp.subst y va.toExp e) hz' hγ']
    congr 1
    apply Exp.subst_openVar_comm
    · exact Ne.symm hyz
    · exact Val.toExp_lc_at_zero hvcl

/-! ## 19. substEnv-openVal: key lemma for lam/letin cases -/

/-- When z ∉ dom(γ) and the closed body equals substEnv γ e,
    substEnv ((z,va)::γ) (e.openVar 0 z) = body.openVal 0 va. -/
-- Subst commutes with openExp when u is closed (u.fv = []) and v has lc_at 0
-- (no BVars in the substituted expression — needed for the fvar y=x case).
private theorem Exp.subst_openExp_comm (e : Exp) (k : Nat) (x : EVar) (u v : Exp)
    (hu : u.fv = []) (hlc_v : Exp.lc_at 0 v) :
    Exp.subst x v (Exp.openExp k u e) = Exp.openExp k u (Exp.subst x v e) := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openExp, Exp.subst]
    by_cases hjk : j = k
    · subst hjk; simp
      exact Exp.subst_closed x v u hu
    · simp only [if_neg hjk, Exp.subst]
  | fvar y =>
    simp only [Exp.openExp, Exp.subst]
    by_cases hyx : y = x
    · subst hyx; simp
      -- need openExp k u v = v; follows from lc_at 0 v (hence lc_at k v)
      exact (Exp.openExp_of_lc_at v k u (Exp.lc_at_mono v (Nat.zero_le k) hlc_v)).symm
    · simp only [if_neg hyx, Exp.openExp]
  | iconst _ => rfl
  | bconst _ => rfl
  | lam body ih =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih (k+1)
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih₁ k; exact ih₂ (k+1)
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih₁ k; exact ih₂ k
  | ann e t ih =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih k
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih₁ k; exact ih₂ k
  | not e ih =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih k
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih₁ k; exact ih₂ k
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.openExp, Exp.subst]
    rw [ih₀ k, ih₁ k, ih₂ k]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openExp, Exp.subst]; congr 1; exact ih₁ k; exact ih₂ k

-- substEnv commutes with openExp when u is closed and all vals in γ satisfy Val.lc
private theorem Exp.substEnv_openExp_comm (e : Exp) (k : Nat) (u : Exp)
    (γ : List (EVar × Val)) (hγ : Subst.AllClosed γ) (hu : u.fv = []) :
    Exp.substEnv γ (Exp.openExp k u e) = Exp.openExp k u (Exp.substEnv γ e) := by
  induction γ generalizing e with
  | nil => simp [Exp.substEnv]
  | cons head tail ih =>
    obtain ⟨y, va⟩ := head
    obtain ⟨hlc_va, hγ'⟩ := hγ
    simp only [Exp.substEnv]
    rw [← ih (Exp.subst y va.toExp e) hγ']
    congr 1
    exact Exp.subst_openExp_comm e k y u va.toExp hu (Val.toExp_lc_at_zero hlc_va)

theorem Exp.substEnv_cons_openVar
    (e : Exp) (γ : List (EVar × Val)) (va : Val) (z : EVar)
    (_ : z ∉ Subst.dom γ) (hγ : Subst.AllClosed γ)
    (hz_fv : z ∉ e.fv) (hva : Val.closed va) :
    Exp.substEnv ((z, va) :: γ) (Exp.openVar 0 z e) =
      Exp.openVal 0 va (Exp.substEnv γ e) := by
  simp only [Exp.substEnv]
  -- subst z va.toExp (openVar 0 z e) = openExp 0 va.toExp e
  rw [Exp.subst_openVar e 0 z va.toExp hz_fv]
  -- substEnv γ (openExp 0 va.toExp e) = openExp 0 va.toExp (substEnv γ e)
  exact Exp.substEnv_openExp_comm e 0 va.toExp γ hγ (Val.toExp_closed_of_closed hva)

/-! ## 19b. substEnv cons-redundant: prepending an already-present binding -/

/-- If x is already mapped to va in γ, prepending (x, va) is redundant. -/
theorem Exp.substEnv_cons_redundant (e : Exp) (γ : List (EVar × Val)) (x : EVar) (va : Val)
    (hlk : Subst.lookup x γ = some va) (hγcl : Subst.AllVClosed γ) :
    Exp.substEnv ((x, va) :: γ) e = Exp.substEnv γ e := by
  induction e generalizing x va γ with
  | bvar _ | iconst _ | bconst _ => simp_all
  | fvar x' =>
    simp only [Exp.substEnv, Exp.subst]
    by_cases h : x' = x
    · -- x' is the same variable being substituted: subst replaces it with va.toExp
      subst h
      simp only
      -- Derive Val.closed va from hlk and hγcl
      have hcl_va : Val.closed va := by
        induction γ with
        | nil => simp [Subst.lookup] at hlk
        | cons head tl ih =>
          obtain ⟨z, w⟩ := head
          obtain ⟨hwcl, hγ'⟩ := hγcl
          simp only [Subst.lookup] at hlk
          by_cases hxz : x' = z
          · subst hxz; simp at hlk; exact hlk ▸ hwcl
          · simp [hxz] at hlk; exact ih hγ' hlk
      have := Exp.substEnv_var_lookup x' γ va hlk hcl_va hγcl
      rw [this]
      rw [Exp.substEnv_closed]
      simp
      simp at hcl_va
      simp
      cases va <;> simp_all [fv, Val.fv]
    · -- x' is a different variable: substitution leaves fvar x' unchanged
      simp only [if_neg h]
  | lam e ih | not e ih | ann e _  ih =>
    simp [substEnv]
    rw [←ih γ x va hlk hγcl]
    simp [Exp.subst, substEnv]
  | letin e₁ e₂ ih1 ih2 | app e₁ e₂ ih1 ih2
  | and e₁ e₂ ih1 ih2 | leq e₁ e₂ ih1 ih2
  | add e₁ e₂ ih1 ih2 =>
    simp [substEnv]
    rw [←ih1 γ x va hlk hγcl, ←ih2 γ x va hlk hγcl]
    simp [Exp.subst, substEnv]
  | ite e₀ e₁ e₂ ih1 ih2 ih3 =>
    simp [substEnv]
    rw [←ih1 γ x va hlk hγcl, ←ih2 γ x va hlk hγcl, ←ih3 γ x va hlk hγcl]
    simp [Exp.subst, substEnv]


  -- substEnv ((x,va)::γ) e = substEnv γ (subst x va.toExp e)
  -- = substEnv γ e, since γ already substitutes x → va.toExp
  -- sorry

/-! ## 20. Formula.interp rename: interpretation is invariant under renaming the opened variable -/

/-- Term-level rename: when φ has no free occurrences of x or y (both fresh),
    opening with x vs y gives equivalent interpretations modulo ρ/ρ' agreement.
    Proved by induction on the Term; see Note [LN-rename] for the proof idea. -/
private theorem Term.interp_openBVar_rename {b' : Base} (t : Term b') (b : Base)
    (x y : EVar) (ρ ρ' : REnv)
    (hx : x ∉ t.fv) (hy : y ∉ t.fv)
    (hval : ρ.get b x = ρ'.get b y)
    (hother_int  : ∀ z, z ≠ x → z ≠ y → ρ.ints  z = ρ'.ints  z)
    (hother_bool : ∀ z, z ≠ x → z ≠ y → ρ.bools z = ρ'.bools z) :
    Term.interp ρ (t.openBVar b 0 x) = Term.interp ρ' (t.openBVar b 0 y) := by
  induction t with
  | const b'' c => simp [Term.openBVar, Term.interp]
  | bvar b'' j =>
    by_cases hbb : b = b'' ∧ j = 0
    · rw [hbb.1]
      by_cases h : b'' = .int
      · rw [h] ; simp [openBVar]
        rw [hbb.2] ; simp [interp] ; grind
      · have h : b'' = Base.bool := by grind
        rw [h] ; simp [openBVar]
        rw [hbb.2] ; simp [interp] ; grind
    · simp at hbb
      by_cases hb : b = b''
      · rw [hb]
        by_cases h : b'' = .int
        · rw [h] ; simp [openBVar]
          simp [hbb hb, interp]
        · have h : b'' = Base.bool := by grind
          rw [h] ; simp [openBVar]
          simp [hbb hb, interp]
      · by_cases h : b = .int
        · have : b'' = .bool := by
            cases b'' <;> grind
          rw [h, this] ; simp [openBVar, interp]
        · have h : b = .bool := by grind
          have : b'' = .int := by
            cases b'' <;> grind
          rw [h, this] ; simp [openBVar, interp]
  | fvar b'' z =>
    have hxz : x ≠ z := fun h => hx (by subst h; simp [Term.fv])
    have hyz : y ≠ z := fun h => hy (by subst h; simp [Term.fv])
    simp only [Term.openBVar, Term.interp]
    cases b'' with
    | int  =>
      cases b with
      | int  => simp [REnv.get]; exact hother_int z (Ne.symm hxz) (Ne.symm hyz)
      | bool => grind
    | bool =>
      cases b with
      | int  => grind
      | bool => simp [REnv.get]; exact hother_bool z (Ne.symm hxz) (Ne.symm hyz)
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.openBVar, Term.interp]
    have hx₁ : x ∉ t₁.fv := fun h => hx (by simp [Term.fv]; grind)
    have hx₂ : x ∉ t₂.fv := fun h => hx (by simp [Term.fv]; grind)
    have hy₁ : y ∉ t₁.fv := fun h => hy (by simp [Term.fv]; grind)
    have hy₂ : y ∉ t₂.fv := fun h => hy (by simp [Term.fv]; grind)
    rw [ih₁ hx₁ hy₁,
        ih₂ hx₂ hy₂]
  | not t ih =>
    simp only [Term.openBVar, Term.interp]
    have hx' : x ∉ t.fv := fun h => hx (by simp [Term.fv]; exact h)
    have hy' : y ∉ t.fv := fun h => hy (by simp [Term.fv]; exact h)
    rw [ih hx' hy']
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.openBVar, Term.interp]
    have hx₁ : x ∉ t₁.fv := fun h => hx (by simp [Term.fv]; grind)
    have hx₂ : x ∉ t₂.fv := fun h => hx (by simp [Term.fv]; grind)
    have hy₁ : y ∉ t₁.fv := fun h => hy (by simp [Term.fv]; grind)
    have hy₂ : y ∉ t₂.fv := fun h => hy (by simp [Term.fv]; grind)
    rw [ih₁ hx₁ hy₁,
        ih₂ hx₂ hy₂]

/-- Rename the opened variable from x to y in Formula.interp, when both x and y
    are fresh for φ (not in φ.fv). In practice φ contains no bvars at level > 0
    (openBVar only replaces level 0) and x, y are expression-level fresh names
    that don't coincide with φ's named quantifier binders. The named-quantifier
    cases (allI/allB/exI/exB) hold by the same argument since updating a binder
    name ≠ x,y leaves x and y slots unchanged. -/
theorem Formula.interp_openBVar_rename (κ : KEnv) (φ : Formula) (b : Base)
    (x y : EVar) (ρ ρ' : REnv)
    (hx : x ∉ φ.fv) (hy : y ∉ φ.fv)
    (hxn : x ∉ φ.named) (hyn : y ∉ φ.named)
    (hval_int  : ρ.ints  x = ρ'.ints  y)
    (hval_bool : ρ.bools x = ρ'.bools y)
    (hother_int  : ∀ z, z ≠ x → z ≠ y → ρ.ints  z = ρ'.ints  z)
    (hother_bool : ∀ z, z ≠ x → z ≠ y → ρ.bools z = ρ'.bools z) :
    Formula.interp κ ρ (φ.openBVar b 0 x) ↔ Formula.interp κ ρ' (φ.openBVar b 0 y) := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  -- Generalize all mutable hypotheses before induction
  revert hx hy hxn hyn hval_int hval_bool hother_int hother_bool ρ ρ'
  induction φ with
  | tt => intros; simp [Formula.openBVar, Formula.interp]
  | ff => intros; simp [Formula.openBVar, Formula.interp]
  | eqI t₁ t₂ =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp only [Formula.openBVar, Formula.interp]
    have hval' : ρ.get b x = ρ'.get b y := by cases b <;> simp [REnv.get, hvi, hvb]
    have h₁ := Term.interp_openBVar_rename t₁ b x y ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hval' hoi hob
    have h₂ := Term.interp_openBVar_rename t₂ b x y ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hval' hoi hob
    rw [h₁, h₂]
  | eqB t₁ t₂ =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp only [Formula.openBVar, Formula.interp]
    have hval' : ρ.get b x = ρ'.get b y := by cases b <;> simp [REnv.get, hvi, hvb]
    have h₁ := Term.interp_openBVar_rename t₁ b x y ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hval' hoi hob
    have h₂ := Term.interp_openBVar_rename t₂ b x y ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hval' hoi hob
    rw [h₁, h₂]
  | leqI t₁ t₂ =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp only [Formula.openBVar, Formula.interp]
    have hval' : ρ.get b x = ρ'.get b y := by cases b <;> simp [REnv.get, hvi, hvb]
    have h₁ := Term.interp_openBVar_rename t₁ b x y ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hval' hoi hob
    have h₂ := Term.interp_openBVar_rename t₂ b x y ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hval' hoi hob
    rw [h₁, h₂]
  | and φ₁ φ₂ ih₁ ih₂ =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(ih₁ ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hxn'.1 hyn'.1 hvi hvb hoi hob).mp h1,
             (ih₂ ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hxn'.2 hyn'.2 hvi hvb hoi hob).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(ih₁ ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hxn'.1 hyn'.1 hvi hvb hoi hob).mpr h1,
             (ih₂ ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hxn'.2 hyn'.2 hvi hvb hoi hob).mpr h2⟩
  | or φ₁ φ₂ ih₁ ih₂ =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl ((ih₁ ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hxn'.1 hyn'.1 hvi hvb hoi hob).mp h1)
      · exact Or.inr ((ih₂ ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hxn'.2 hyn'.2 hvi hvb hoi hob).mp h2)
    · rintro (h1 | h2)
      · exact Or.inl ((ih₁ ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hxn'.1 hyn'.1 hvi hvb hoi hob).mpr h1)
      · exact Or.inr ((ih₂ ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hxn'.2 hyn'.2 hvi hvb hoi hob).mpr h2)
  | not φ ih =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    exact not_congr (ih ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    constructor
    · intro hf h1
      exact (ih₂ ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hxn'.2 hyn'.2 hvi hvb hoi hob).mp
        (hf ((ih₁ ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hxn'.1 hyn'.1 hvi hvb hoi hob).mpr h1))
    · intro hf h1
      exact (ih₂ ρ ρ' (not_mem_r x _ _ hx') (not_mem_r y _ _ hy') hxn'.2 hyn'.2 hvi hvb hoi hob).mpr
        (hf ((ih₁ ρ ρ' (not_mem_l x _ _ hx') (not_mem_l y _ _ hy') hxn'.1 hyn'.1 hvi hvb hoi hob).mp h1))
  | exI x' φ ih | exB x' φ ih=>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    constructor
    · intro ⟨n, hf⟩
      exists n
      grind
    · intro ⟨n, hf⟩
      exists n
      grind
  | allI x' φ ih =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    constructor
    · intro hf n
      -- x ≠ x' and y ≠ x' come from hxn'.1 and hyn'.1
      have xf : x ∉ φ.fv := by grind
      have yf : y ∉ φ.fv := by grind
      -- Conditions for IH applied to updated envs
      have hvi' : (ρ.update .int x' n).ints x = (ρ'.update .int x' n).ints y := by
        simp only
        simp [beq_eq_false_iff_ne.mpr (Ne.symm hxn'.1),
              beq_eq_false_iff_ne.mpr (Ne.symm hyn'.1), hvi]
      have hvb' : (ρ.update .int x' n).bools x = (ρ'.update .int x' n).bools y := by
        simp [hvb]
      have hoi' : ∀ z, z ≠ x → z ≠ y → (ρ.update .int x' n).ints z = (ρ'.update .int x' n).ints z := by
        intro z hnx hnz
        simp only
        by_cases hzx' : x' = z
        · subst hzx'; simp
        · simp [beq_eq_false_iff_ne.mpr hzx', hoi z hnx hnz]
      have hob' : ∀ z, z ≠ x → z ≠ y → (ρ.update .int x' n).bools z = (ρ'.update .int x' n).bools z := by
        intro z hnx hnz; simp [hob z hnx hnz]
      exact (ih (ρ.update .int x' n) (ρ'.update .int x' n) xf yf hxn'.2 hyn'.2
                hvi' hvb' hoi' hob').mp (hf n)
    · intro hf n
      -- x ≠ x' and y ≠ x' come from hxn'.1 and hyn'.1
      have xf : x ∉ φ.fv := by grind
      have yf : y ∉ φ.fv := by grind
      -- Conditions for IH applied to updated envs
      have hvi' : (ρ.update .int x' n).ints x = (ρ'.update .int x' n).ints y := by
        simp only
        simp [beq_eq_false_iff_ne.mpr (Ne.symm hxn'.1),
              beq_eq_false_iff_ne.mpr (Ne.symm hyn'.1), hvi]
      have hvb' : (ρ.update .int x' n).bools x = (ρ'.update .int x' n).bools y := by
        simp [hvb]
      have hoi' : ∀ z, z ≠ x → z ≠ y → (ρ.update .int x' n).ints z = (ρ'.update .int x' n).ints z := by
        intro z hnx hnz
        simp only
        by_cases hzx' : x' = z
        · subst hzx'; simp
        · simp [beq_eq_false_iff_ne.mpr hzx', hoi z hnx hnz]
      have hob' : ∀ z, z ≠ x → z ≠ y → (ρ.update .int x' n).bools z = (ρ'.update .int x' n).bools z := by
        intro z hnx hnz; simp [hob z hnx hnz]
      exact (ih (ρ.update .int x' n) (ρ'.update .int x' n) xf yf hxn'.2 hyn'.2
                hvi' hvb' hoi' hob').mpr (hf n)
  | allB x' φ ih =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv] at hx' hy'
    simp [Formula.named] at hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    constructor
    · intro hf b
      -- x ≠ x' and y ≠ x' come from hxn'.1 and hyn'.1
      have xf : x ∉ φ.fv := by grind
      have yf : y ∉ φ.fv := by grind
      -- Conditions for IH applied to updated envs
      have hvi' : (ρ.update .bool x' b).bools x = (ρ'.update .bool x' b).bools y := by
        simp only
        simp [beq_eq_false_iff_ne.mpr (Ne.symm hxn'.1),
              beq_eq_false_iff_ne.mpr (Ne.symm hyn'.1), hvb]
      have hvb' : (ρ.update .bool x' b).ints x = (ρ'.update .bool x' b).ints y := by
        simp [hvi]
      have hoi' : ∀ z, z ≠ x → z ≠ y → (ρ.update .bool x' b).bools z = (ρ'.update .bool x' b).bools z := by
        intro z hnx hnz
        simp only
        by_cases hzx' : x' = z
        · subst hzx'; simp
        · simp [beq_eq_false_iff_ne.mpr hzx', hob z hnx hnz]
      have hob' : ∀ z, z ≠ x → z ≠ y → (ρ.update .bool x' b).ints z = (ρ'.update .bool x' b).ints z := by
        intro z hnx hnz; simp [hoi z hnx hnz]
      exact (ih (ρ.update .bool x' b) (ρ'.update .bool x' b) xf yf hxn'.2 hyn'.2
                hvb' hvi' hob' hoi').mp (hf b)
    · intro hf n
      -- x ≠ x' and y ≠ x' come from hxn'.1 and hyn'.1
      have xf : x ∉ φ.fv := by grind
      have yf : y ∉ φ.fv := by grind
      -- Conditions for IH applied to updated envs
      have hvi' : (ρ.update .bool x' n).bools x = (ρ'.update .bool x' n).bools y := by
        simp only
        simp [beq_eq_false_iff_ne.mpr (Ne.symm hxn'.1),
              beq_eq_false_iff_ne.mpr (Ne.symm hyn'.1), hvb]
      have hvb' : (ρ.update .bool x' n).ints x = (ρ'.update .bool x' n).ints y := by
        simp [hvi]
      have hoi' : ∀ z, z ≠ x → z ≠ y → (ρ.update .bool x' n).bools z = (ρ'.update .bool x' n).bools z := by
        intro z hnx hnz
        simp only
        by_cases hzx' : x' = z
        · subst hzx'; simp
        · simp [beq_eq_false_iff_ne.mpr hzx', hob z hnx hnz]
      have hob' : ∀ z, z ≠ x → z ≠ y → (ρ.update .bool x' n).ints z = (ρ'.update .bool x' n).ints z := by
        intro z hnx hnz; simp [hoi z hnx hnz]
      exact (ih (ρ.update .bool x' n) (ρ'.update .bool x' n) xf yf hxn'.2 hyn'.2
                hvb' hvi' hob' hoi').mpr (hf n)
  | kapp kname args =>
    intro ρ ρ' hx' hy' hxn' hyn' hvi hvb hoi hob
    simp only [Formula.fv, Formula.named] at hx' hy' hxn' hyn'
    simp only [Formula.openBVar, Formula.interp]
    -- Show the two argument lists are equal by renaming each term
    have hargs : args.map (fun a => (⟨a.1, Term.interp ρ (a.2.openBVar b 0 x)⟩ : Σ b : Base, b.interp)) =
                 args.map (fun a => (⟨a.1, Term.interp ρ' (a.2.openBVar b 0 y)⟩ : Σ b : Base, b.interp)) := by
      apply List.map_congr_left
      intro a ha
      have hxa : x ∉ a.2.fv := fun hmem =>
        hx' (List.mem_flatMap.mpr ⟨a, ha, hmem⟩)
      have hya : y ∉ a.2.fv := fun hmem =>
        hy' (List.mem_flatMap.mpr ⟨a, ha, hmem⟩)
      have hval' : ρ.get b x = ρ'.get b y := by cases b <;> simp [REnv.get, hvi, hvb]
      congr 1
      exact Term.interp_openBVar_rename a.2 b x y ρ ρ' hxa hya hval' hoi hob
    rw [List.map_map, List.map_map, Function.comp_def, Function.comp_def]
    simp
    rw [hargs]
/-! ## 20. Formula.interp freshness under env updates

  When `x ∉ fv φ` AND `x ∉ named φ` (i.e. x is not used as a binder in φ),
  updating ρ at x does not affect `Formula.interp κ ρ φ`. -/

theorem Formula.interp_update_fresh_int (κ : KEnv) (φ : Formula)
    (x : EVar) (w : Int) (ρ : REnv)
    (hfv : x ∉ φ.fv) (hnamed : x ∉ φ.named) :
    Formula.interp κ ρ φ ↔ Formula.interp κ (ρ.update .int x w) φ := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  induction φ generalizing ρ with
  | tt => simp [Formula.interp]
  | ff => simp [Formula.interp]
  | eqI t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    rw [Term.interp_update_fresh_int t₁ x w ρ (not_mem_l _ _ _ hfv),
        Term.interp_update_fresh_int t₂ x w ρ (not_mem_r _ _ _ hfv)]
  | eqB t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    rw [Term.interp_update_fresh_int t₁ x w ρ (not_mem_l _ _ _ hfv),
        Term.interp_update_fresh_int t₂ x w ρ (not_mem_r _ _ _ hfv)]
  | leqI t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    rw [Term.interp_update_fresh_int t₁ x w ρ (not_mem_l _ _ _ hfv),
        Term.interp_update_fresh_int t₂ x w ρ (not_mem_r _ _ _ hfv)]
  | and φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | not φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | exI y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    -- x ≠ y because x ∉ named (exI y φ) = y :: named φ
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    -- x ∉ fv φ: since x ≠ y and x ∉ filter (≠ y) (fv φ), we get x ∉ fv φ
    have hxf : x ∉ φ.fv := by
      intro hmem
      exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← REnv.update_comm_int_int ρ y x n w (Ne.symm hxy)]
      grind
    · intro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← REnv.update_comm_int_int ρ y x n w (Ne.symm hxy)] at hn
      grind
  | exB y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [← REnv.update_comm_int_bool ρ x y w b]
      grind
    · intro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [← REnv.update_comm_int_bool ρ x y w b] at hb
      grind
  | allI y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro h n
      rw [← REnv.update_comm_int_int ρ y x n w (Ne.symm hxy)]
      exact (ih (ρ.update .int y n) hxf hxn ).mp (h n)
    · intro h n
      exact (ih (ρ.update .int y n) hxf hxn ).mpr (REnv.update_comm_int_int ρ y x n w (Ne.symm hxy) ▸ (h n))
  | allB y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro h b
      rw [← REnv.update_comm_int_bool ρ x y w b]
      exact (ih (ρ.update .bool y b) hxf hxn).mp (h b)
    · intro h b
      exact (ih (ρ.update .bool y b) hxf hxn).mpr (REnv.update_comm_int_bool ρ x y w b ▸ (h b))
  | kapp kname args =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    suffices heq : args.map (fun a => (⟨a.1, Term.interp ρ a.2⟩ : Σ b : Base, b.interp)) =
                   args.map (fun a => (⟨a.1, Term.interp (ρ.update .int x w) a.2⟩ : Σ b : Base, b.interp)) by
      rw [heq]
    apply List.map_congr_left
    intro a ha
    have hxa : x ∉ a.2.fv := fun hmem =>
      hfv (List.mem_flatMap.mpr ⟨a, ha, hmem⟩)
    simp only [Term.interp_update_fresh_int a.2 x w ρ hxa]

theorem Formula.interp_update_fresh_bool (κ : KEnv) (φ : Formula)
    (x : EVar) (w : Bool) (ρ : REnv)
    (hfv : x ∉ φ.fv) (hnamed : x ∉ φ.named) :
    Formula.interp κ ρ φ ↔ Formula.interp κ (ρ.update .bool x w) φ := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  induction φ generalizing ρ with
  | tt => simp [Formula.interp]
  | ff => simp [Formula.interp]
  | eqI t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    rw [Term.interp_update_fresh_bool t₁ x w ρ (not_mem_l _ _ _ hfv),
        Term.interp_update_fresh_bool t₂ x w ρ (not_mem_r _ _ _ hfv)]
  | eqB t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    rw [Term.interp_update_fresh_bool t₁ x w ρ (not_mem_l _ _ _ hfv),
        Term.interp_update_fresh_bool t₂ x w ρ (not_mem_r _ _ _ hfv)]
  | leqI t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    rw [Term.interp_update_fresh_bool t₁ x w ρ (not_mem_l _ _ _ hfv),
        Term.interp_update_fresh_bool t₂ x w ρ (not_mem_r _ _ _ hfv)]
  | and φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | not φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    exact not_congr (ih ρ hfv hnamed)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | exI y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← REnv.update_comm_int_bool ρ y x n w]
      exact (ih (ρ.update .int y n) hxf hxn).mp hn
    · intro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← REnv.update_comm_int_bool ρ y x n w] at hn
      exact (ih (ρ.update .int y n) hxf hxn).mpr hn
  | exB y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [← REnv.update_comm_bool_bool ρ y x b w (Ne.symm hxy)]
      exact (ih (ρ.update .bool y b) hxf hxn).mp hb
    · intro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [← REnv.update_comm_bool_bool ρ y x b w (Ne.symm hxy)] at hb
      exact (ih (ρ.update .bool y b) hxf hxn).mpr hb
  | allI y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro h n
      rw [← REnv.update_comm_int_bool ρ y x n w]
      exact (ih (ρ.update .int y n) hxf hxn).mp (h n)
    · intro h n
      exact (ih (ρ.update .int y n) hxf hxn).mpr (REnv.update_comm_int_bool ρ y x n w ▸ (h n))
  | allB y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := by
      intro hmem; exact hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    constructor
    · intro h b
      rw [← REnv.update_comm_bool_bool ρ y x b w (Ne.symm hxy)]
      exact (ih (ρ.update .bool y b) hxf hxn).mp (h b)
    · intro h b
      have hb := h b
      rw [← REnv.update_comm_bool_bool ρ y x b w (Ne.symm hxy)] at hb
      exact (ih (ρ.update .bool y b) hxf hxn).mpr hb
  | kapp kname args =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    suffices heq : args.map (fun a => (⟨a.1, Term.interp ρ a.2⟩ : Σ b : Base, b.interp)) =
                   args.map (fun a => (⟨a.1, Term.interp (ρ.update .bool x w) a.2⟩ : Σ b : Base, b.interp)) by
      rw [heq]
    apply List.map_congr_left
    intro a ha
    have hxa : x ∉ a.2.fv := fun hmem =>
      hfv (List.mem_flatMap.mpr ⟨a, ha, hmem⟩)
    simp only [Term.interp_update_fresh_bool a.2 x w ρ hxa]

/-! ## REnv update commutativity
  These lemmas let us reorder two independent updates to `REnv`.
  Proofs by `REnv.ext` + pointwise function extensionality. -/

theorem REnv.update_int_int_comm (ρ : REnv) (x y : EVar) (hxy : x ≠ y)
    (m n : Int) :
    (ρ.update .int x m).update .int y n = (ρ.update .int y n).update .int x m := by
  apply REnv.ext
  · funext z
    simp
    by_cases hzx : x = z <;> by_cases hzy : y = z <;>
      simp_all
  · rfl

theorem REnv.update_bool_bool_comm (ρ : REnv) (x y : EVar) (hxy : x ≠ y)
    (m n : Bool) :
    (ρ.update .bool x m).update .bool y n = (ρ.update .bool y n).update .bool x m := by
  apply REnv.ext
  · rfl
  · funext z
    simp
    by_cases hzx : x = z <;> by_cases hzy : y = z <;>
      simp_all

theorem REnv.update_int_bool_comm (ρ : REnv) (x y : EVar) (m : Int) (n : Bool) :
    (ρ.update .int x m).update .bool y n = (ρ.update .bool y n).update .int x m := by
  apply REnv.ext <;> rfl

/-- If `x ∉ r.fmla.fv.filter (· ≠ nuName)` and `x ≠ nuName`, then `x ∉ r.fmla.fv`. -/
theorem Refinement.fv_filter_of_ne_nu {b : Base} (r : Refinement b) (x : EVar)
    (hx : x ∉ r.fv) (hxν : x ≠ nuName) : x ∉ r.fmla.fv := by
  simp only [Refinement.fv, List.mem_filter] at hx
  intro hmem
  grind

/-! ## fv/named monotonicity under openVar -/

/-- Opening a `Term` with `z` can only add `z` to the free variables. -/
private theorem Term.fv_openBVar_subset {b : Base} (b' : Base) (k : Nat) (z : EVar)
    (t : Term b) : ∀ y ∈ Term.fv (Term.openBVar b' k z t), y = z ∨ y ∈ Term.fv t := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.fv]
  | bvar b'' j =>
    intro y hy
    cases b'' <;> cases b' <;> simp only [Term.openBVar, Term.fv] at hy ⊢ <;>
    (by_cases h : j = k <;> simp_all [Term.fv])
  | fvar _ _ =>
    intro y hy; simp only [Term.openBVar, Term.fv, List.mem_singleton] at hy ⊢; exact Or.inr (by simpa)
  | add t₁ t₂ ih₁ ih₂ =>
    intro y hy
    simp only [Term.openBVar, Term.fv, List.mem_append] at hy ⊢
    rcases hy with h | h
    · rcases ih₁ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases ih₂ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
  | not t ih =>
    simp only [Term.openBVar, Term.fv]; exact ih
  | and t₁ t₂ ih₁ ih₂ =>
    intro y hy
    simp only [Term.openBVar, Term.fv, List.mem_append] at hy ⊢
    rcases hy with h | h
    · rcases ih₁ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases ih₂ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')

/-- Opening a `Formula` with `z` can only add `z` to the free variables. -/
private theorem Formula.fv_openBVar_subset (b' : Base) (k : Nat) (z : EVar)
    (φ : Formula) : ∀ y ∈ Formula.fv (φ.openBVar b' k z), y = z ∨ y ∈ Formula.fv φ := by
  induction φ with
  | tt | ff => simp [Formula.openBVar, Formula.fv]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    intro y hy
    simp only [Formula.openBVar, Formula.fv, List.mem_append] at hy ⊢
    rcases hy with h | h
    · rcases Term.fv_openBVar_subset b' k z t₁ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases Term.fv_openBVar_subset b' k z t₂ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    intro y hy
    simp only [Formula.openBVar, Formula.fv, List.mem_append] at hy ⊢
    rcases hy with h | h
    · rcases ih₁ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases ih₂ y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
  | not φ ih =>
    simp only [Formula.openBVar, Formula.fv]; exact ih
  | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
    intro y hy
    simp only [Formula.openBVar, Formula.fv, List.mem_filter] at hy ⊢
    obtain ⟨hy_mem, hy_ne⟩ := hy
    rcases ih y hy_mem with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hy_ne⟩
  | kapp name args =>
    intro y hy
    simp only [Formula.openBVar, Formula.fv, List.mem_flatMap, List.mem_map] at hy ⊢
    obtain ⟨a, ⟨a₀, ha₀_mem, rfl⟩, hy_in⟩ := hy
    rcases Term.fv_openBVar_subset b' k z a₀.2 y hy_in with h | h
    · exact Or.inl h
    · exact Or.inr ⟨a₀, ha₀_mem, h⟩

/-- Opening `Ty` with `z` doesn't add any `x ≠ z` to the free variables. -/
theorem Ty.fv_openVar_not_mem (t : Ty) (k : Nat) (z x : EVar)
    (hx : x ∉ t.fv) (hxz : x ≠ z) : x ∉ (t.openVar k z).fv := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.openVar, Ty.fv, Refinement.fv, Refinement.openBVar]
    intro hmem
    simp only [List.mem_filter] at hmem
    obtain ⟨hmem', hnu⟩ := hmem
    -- hmem' : x ∈ (r.fmla.openBVar .int k z).openBVar .bool k z).fv
    have hstep : ∀ y ∈ Formula.fv ((r.fmla.openBVar .int k z).openBVar .bool k z), y = z ∨ y ∈ Formula.fv r.fmla := by
      intro y hy
      rcases Formula.fv_openBVar_subset .bool k z _ y hy with h | h
      · exact Or.inl h
      · rcases Formula.fv_openBVar_subset .int k z r.fmla y h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
    rcases hstep x hmem' with h | h
    · exact hxz h
    · apply hx; simp only [Ty.fv, Refinement.fv, List.mem_filter]; exact ⟨h, hnu⟩
  | arrow s t ihs iht =>
    simp only [Ty.openVar, Ty.fv, List.mem_append, not_or]
    simp only [Ty.fv, List.mem_append, not_or] at hx
    exact ⟨ihs k hx.1, iht (k + 1) hx.2⟩

/-- Opening `Ty` with `z` doesn't add any `x ≠ z` to the named binders. -/
theorem Ty.named_openVar_not_mem (t : Ty) (k : Nat) (z x : EVar)
    (hx : x ∉ Ty.named t) (hxz : x ≠ z) : x ∉ Ty.named (t.openVar k z) := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.openVar, Ty.named, Refinement.openBVar]
    -- Need: x ∉ (r.fmla.openBVar .int k z).openBVar .bool k z).named
    simp only [Ty.named] at hx
    -- Show named is preserved under openBVar (binder names unchanged, kapp adds only z)
    suffices h : ∀ (φ : Formula), x ∉ φ.named → x ∉ (φ.openBVar .bool k z).named by
      apply h
      suffices h2 : ∀ (φ : Formula), x ∉ φ.named → x ∉ (φ.openBVar .int k z).named from
        h2 r.fmla hx
      intro φ hφ
      induction φ with
      | tt | ff | eqI _ _ | eqB _ _ | leqI _ _ => simp [Formula.openBVar, Formula.named]
      | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
        simp only [Formula.openBVar, Formula.named, List.mem_append, not_or] at *
        exact ⟨ih₁ hφ.1, ih₂ hφ.2⟩
      | not φ ih => simp [Formula.openBVar, Formula.named] at *; exact ih hφ
      | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
        simp only [Formula.openBVar, Formula.named, List.mem_cons, not_or] at *
        exact ⟨hφ.1, ih hφ.2⟩
      | kapp name args =>
        simp only [Formula.openBVar, Formula.named, List.mem_flatMap, List.mem_map] at *
        intro hx_mem
        apply hφ
        obtain ⟨a, ⟨a₀, ha₀_mem, rfl⟩, hy_in⟩ := hx_mem
        rcases Term.fv_openBVar_subset .int k z a₀.2 x hy_in with h | h
        · exact absurd h hxz
        · exact ⟨a₀, ha₀_mem, h⟩
    intro φ hφ
    induction φ with
    | tt | ff | eqI _ _ | eqB _ _ | leqI _ _ => simp [Formula.openBVar, Formula.named]
    | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [Formula.openBVar, Formula.named, List.mem_append, not_or] at *
      exact ⟨ih₁ hφ.1, ih₂ hφ.2⟩
    | not φ ih => simp [Formula.openBVar, Formula.named] at *; exact ih hφ
    | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
      simp only [Formula.openBVar, Formula.named, List.mem_cons, not_or] at *
      exact ⟨hφ.1, ih hφ.2⟩
    | kapp name args =>
      simp only [Formula.openBVar, Formula.named, List.mem_flatMap, List.mem_map] at *
      intro hx_mem
      apply hφ
      obtain ⟨a, ⟨a₀, ha₀_mem, rfl⟩, hy_in⟩ := hx_mem
      rcases Term.fv_openBVar_subset .bool k z a₀.2 x hy_in with h | h
      · exact absurd h hxz
      · exact ⟨a₀, ha₀_mem, h⟩
  | arrow s t ihs iht =>
    simp only [Ty.openVar, Ty.named, List.mem_append, not_or] at *
    exact ⟨ihs k hx.1, iht (k + 1) hx.2⟩

end STLC
