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
  | .ann e t       => Exp.fv e ++ t.fv
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
  | k, .ann e t       => e.lc_at k ∧ t.lc_at k
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

private def EVar.maxLen : List EVar → Nat
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
    simp [Exp.fv, List.append_eq_nil_iff] at he
    show Exp.ann (Exp.subst x u e) t = Exp.ann e t
    rw [ih he.1]
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

/-- All values in `γ` are pointwise closed. -/
def Subst.AllVClosed : List (EVar × Val) → Prop
  | []          => True
  | (_, v) :: γ => Val.closed v ∧ Subst.AllVClosed γ

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

end STLC
