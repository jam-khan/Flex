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

/-- Rename all free occurrences of `x` to `y` in a `Term`, preserving base.
    Hits both int and bool slots since `x` may refer to either base. -/
def Term.replaceFVar {b : Base} (x y : EVar) : Term b → Term b
  | .const b c    => .const b c
  | .bvar b j     => .bvar b j
  | .fvar b z     => if z = x then .fvar b y else .fvar b z
  | .add t₁ t₂    => .add (t₁.replaceFVar x y) (t₂.replaceFVar x y)
  | .not t        => .not (t.replaceFVar x y)
  | .and t₁ t₂    => .and (t₁.replaceFVar x y) (t₂.replaceFVar x y)

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

@[simp]
theorem Formula.named_openBVar (b' : Base) (k : Nat) (z : EVar) (φ : Formula) :
    (φ.openBVar b' k z).named = φ.named := by
  induction φ generalizing k with
  | tt | ff | eqI _ _ | eqB _ _ | leqI _ _ => rfl
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp [Formula.openBVar, Formula.named, ih₁ k, ih₂ k]
  | not φ ih => simp [Formula.openBVar, Formula.named, ih k]
  | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp [Formula.openBVar, Formula.named, ih k]

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

/-- Rename all free occurrences of `x` to `y` in a `Formula`. Both int and
    bool slots are renamed (a name may refer to either base in the same
    formula). Named binders shadow: when binder `z = x`, the subtree is left
    alone since the rename target is bound away. -/
def Formula.replaceFVar (x y : EVar) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eqI t₁ t₂    => .eqI (t₁.replaceFVar x y) (t₂.replaceFVar x y)
  | .eqB t₁ t₂    => .eqB (t₁.replaceFVar x y) (t₂.replaceFVar x y)
  | .leqI t₁ t₂   => .leqI (t₁.replaceFVar x y) (t₂.replaceFVar x y)
  | .and φ₁ φ₂    => .and (φ₁.replaceFVar x y) (φ₂.replaceFVar x y)
  | .or φ₁ φ₂     => .or (φ₁.replaceFVar x y) (φ₂.replaceFVar x y)
  | .not φ        => .not (φ.replaceFVar x y)
  | .imp φ₁ φ₂    => .imp (φ₁.replaceFVar x y) (φ₂.replaceFVar x y)
  | .exI z φ      => if z = x then .exI z φ else .exI z (φ.replaceFVar x y)
  | .exB z φ      => if z = x then .exB z φ else .exB z (φ.replaceFVar x y)
  | .allI z φ     => if z = x then .allI z φ else .allI z (φ.replaceFVar x y)
  | .allB z φ     => if z = x then .allB z φ else .allB z (φ.replaceFVar x y)

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

/-- Interpret a (now κ-free) formula in `ρ`. Named existentials extend `ρ` at the
    bound name. No κ-assignment is needed: κ-applications live one level up, in
    `Refinement`, so only `Refinement.interp` consults the κ-assignment. -/
def Formula.interp (ρ : REnv) : Formula → Prop
  | .tt           => True
  | .ff           => False
  | .eqI t₁ t₂    => Term.interp ρ t₁ = Term.interp ρ t₂
  | .eqB t₁ t₂    => Term.interp ρ t₁ = Term.interp ρ t₂
  | .leqI t₁ t₂   => Term.interp ρ t₁ ≤ Term.interp ρ t₂
  | .and φ₁ φ₂    => Formula.interp ρ φ₁ ∧ Formula.interp ρ φ₂
  | .or φ₁ φ₂     => Formula.interp ρ φ₁ ∨ Formula.interp ρ φ₂
  | .not φ        => ¬ Formula.interp ρ φ
  | .imp φ₁ φ₂    => Formula.interp ρ φ₁ → Formula.interp ρ φ₂
  | .exI x φ      => ∃ n : Int,  Formula.interp (ρ.update .int  x n) φ
  | .exB x φ      => ∃ b : Bool, Formula.interp (ρ.update .bool x b) φ
  | .allI x φ     => ∀ n : Int,  Formula.interp (ρ.update .int  x n) φ
  | .allB x φ     => ∀ b : Bool, Formula.interp (ρ.update .bool x b) φ

/-! ## 3. Refinement operations -/

/-- Free variables of a refinement: formula's fv minus `nuName` (ν is "bound"
    semantically by the refinement). -/
def Refinement.fv {b : Base} (r : Refinement b) : List EVar :=
  match r with
  | .fmla φ      => φ.fv.filter (· ≠ nuName)
  | .kapp _ args => (args.flatMap (fun a => Term.fv a.2)).filter (· ≠ nuName)

def Refinement.openBVar (b' : Base) (k : Nat) (x : EVar)
    {b : Base} (r : Refinement b) : Refinement b :=
  match r with
  | .fmla φ       => .fmla (φ.openBVar b' k x)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, Term.openBVar b' k x a.2⟩))

def Refinement.substI (x : EVar) (u : Term .int)
    {b : Base} (r : Refinement b) : Refinement b :=
  match r with
  | .fmla φ       => .fmla (φ.substI x u)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, a.2.substI x u⟩))

def Refinement.substB (x : EVar) (u : Term .bool)
    {b : Base} (r : Refinement b) : Refinement b :=
  match r with
  | .fmla φ       => .fmla (φ.substB x u)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, a.2.substB x u⟩))

/-- Rename free occurrences of `x` to `y` inside a refinement. -/
def Refinement.replaceFVar {b : Base} (x y : EVar) (r : Refinement b) :
    Refinement b :=
  match r with
  | .fmla φ       => .fmla (φ.replaceFVar x y)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, a.2.replaceFVar x y⟩))

def Refinement.lc_at (k : Nat) {b : Base} (r : Refinement b) : Prop :=
  match r with
  | .fmla φ      => φ.lc_at k
  | .kapp _ args => ∀ a ∈ args, Term.lc_at k a.2

/-- Named binders appearing in a refinement (a κ-application binds no names). -/
def Refinement.named {b : Base} (r : Refinement b) : List EVar :=
  match r with
  | .fmla φ   => φ.named
  | .kapp _ _ => []

/-- Interpret a refinement at value ν under κ-assignment: extend ρ at `nuName`
    with ν, then either interpret the formula or apply κ. This is the *only*
    interpretation that consults the κ-assignment. -/
def Refinement.interp (κ : KEnv) {b : Base} (r : Refinement b)
    (ρ : REnv) (ν : b.interp) : Prop :=
  match r with
  | .fmla φ       => Formula.interp (ρ.update b nuName ν) φ
  | .kapp kn args =>
      κ kn (args.map (fun a => ⟨a.1, Term.interp (ρ.update b nuName ν) a.2⟩))

/-- Denotation of a refinement at κ-assignment κ and env ρ: the predicate on
    `b.interp` defining which values satisfy it. Alias for
    `Refinement.interp κ r ρ` (point-free). -/
def Refinement.den (κ : KEnv) {b : Base} (r : Refinement b) (ρ : REnv) :
    b.interp → Prop :=
  fun ν => r.interp κ ρ ν

@[simp] theorem Refinement.den_apply (κ : KEnv) {b : Base} (r : Refinement b)
    (ρ : REnv) (ν : b.interp) : r.den κ ρ ν ↔ r.interp κ ρ ν := Iff.rfl

/-- Refinement type for an integer constant: `{ν : Int | ν = n}`. -/
@[simp] def prim (n : Int) : Ty :=
  .refine .int (.fmla (.eqI (.fvar .int nuName) (.const .int n)))

/-- Refinement type for a boolean constant: `{ν : Bool | ν = b}`. -/
@[simp] def primBool (b : Bool) : Ty :=
  .refine .bool (.fmla (.eqB (.fvar .bool nuName) (.const .bool b)))

/-- `self x t` is the *singleton* refinement `{ν | ν = x}` against the stored
    value of `x` (selfification). The variable's own refinement is recovered
    from the typing context, so it is not re-conjoined here — keeping the
    synthesized type kvar-free. For function types, returns `t` unchanged. -/
@[simp] def self : EVar → Ty → Ty
  | x, .refine .int  _ => .refine .int  (.fmla
      (.eqI (.fvar .int  nuName) (.fvar .int  x)))
  | x, .refine .bool _ => .refine .bool (.fmla
      (.eqB (.fvar .bool nuName) (.fvar .bool x)))
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
  | .refine _ r => r.named
  | .arrow s t  => Ty.named s ++ Ty.named t

/-- Open a `Ty`'s outermost binder at level `k` with free name `x`. Replaces
    `Term.bvar b k` for BOTH bases (int and bool) in every refinement formula.
    In a well-formed type at most one base's BVars appear at each level, so
    one of the two openBVar calls is always a no-op. -/
def Ty.openVar (k : Nat) (x : EVar) : Ty → Ty
  | .refine b r => .refine b ((r.openBVar .int k x).openBVar .bool k x)
  | .arrow s t  => .arrow (s.openVar k x) (t.openVar (k+1) x)

@[simp]
theorem Refinement.named_openBVar {b'' : Base} (b' : Base) (k : Nat) (z : EVar)
    (r : Refinement b'') : (r.openBVar b' k z).named = r.named := by
  cases r with
  | fmla φ => simp [Refinement.openBVar, Refinement.named, Formula.named_openBVar]
  | kapp kn args => simp [Refinement.openBVar, Refinement.named]

@[simp]
theorem Ty.named_openVar (t : Ty) (k : Nat) (z : EVar) :
    (t.openVar k z).named = t.named := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.openVar, Ty.named, Refinement.named_openBVar]
  | arrow s t ihs iht =>
    simp [Ty.openVar, Ty.named, ihs k, iht (k+1)]

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

theorem Ty.openVar_refine_base (t : Ty) (k : Nat) (x y : EVar) (b : Base) {r : Refinement b} :
    t.openVar k x = .refine b r → ∃ r', t.openVar k y = .refine b r' := by
  intro h
  cases t with
  | refine b' r' =>
    simp only [Ty.openVar] at h ⊢
    cases b' <;> cases b <;> simp_all <;> exact ⟨_, rfl⟩
  | arrow _ _ => simp [Ty.openVar] at h

theorem Ty.openVar_refine_arrow (t : Ty) (k : Nat) (x y : EVar) :
    t.openVar k x = .arrow s' t' → ∃ s'' t'', t.openVar k y = .arrow s'' t'' := by
  intro h
  cases t <;> simp [Ty.openVar] at h ⊢


def Ty.substI (x : EVar) (u : Term .int) : Ty → Ty
  | .refine b r => .refine b (r.substI x u)
  | .arrow s t  => .arrow (s.substI x u) (t.substI x u)

def Ty.substB (x : EVar) (u : Term .bool) : Ty → Ty
  | .refine b r => .refine b (r.substB x u)
  | .arrow s t  => .arrow (s.substB x u) (t.substB x u)

/-! ### Value substitution for bound variables (substBV)

  `Term.substBV b' k v t` replaces `Term.bvar b' k` with `Term.const b' v` in `t`.
  This is the semantic counterpart of `Term.openBVar b' k x`: instead of
  substituting a fresh name, we substitute the concrete value directly.

  `Ty.substBV va t` replaces the BVar at level 0 throughout `t` with the
  value carried by `va` — mirroring how coq-SystemRF uses `tsubBV v_x t'`.
  Level shifts by +1 inside each `arrow` binder, mirroring `Ty.openVar`. -/

def Term.substBV (b' : Base) (k : Nat) (v : b'.interp) :
    {b : Base} → Term b → Term b
  | _, .const b c    => .const b c
  | _, .bvar b j     =>
      match b', b with
      | .int,  .int  => if j = k then .const .int  v else .bvar .int  j
      | .bool, .bool => if j = k then .const .bool v else .bvar .bool j
      | .int,  .bool => .bvar .bool j
      | .bool, .int  => .bvar .int  j
  | _, .fvar b x     => .fvar b x
  | _, .add t₁ t₂    => .add (Term.substBV b' k v t₁) (Term.substBV b' k v t₂)
  | _, .not t        => .not (Term.substBV b' k v t)
  | _, .and t₁ t₂    => .and (Term.substBV b' k v t₁) (Term.substBV b' k v t₂)

def Formula.substBV (b : Base) (k : Nat) (v : b.interp) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eqI t₁ t₂    => .eqI (t₁.substBV b k v) (t₂.substBV b k v)
  | .eqB t₁ t₂    => .eqB (t₁.substBV b k v) (t₂.substBV b k v)
  | .leqI t₁ t₂   => .leqI (t₁.substBV b k v) (t₂.substBV b k v)
  | .and φ₁ φ₂    => .and (φ₁.substBV b k v) (φ₂.substBV b k v)
  | .or φ₁ φ₂     => .or (φ₁.substBV b k v) (φ₂.substBV b k v)
  | .not φ        => .not (φ.substBV b k v)
  | .imp φ₁ φ₂    => .imp (φ₁.substBV b k v) (φ₂.substBV b k v)
  | .exI y φ      => .exI y (φ.substBV b k v)
  | .exB y φ      => .exB y (φ.substBV b k v)
  | .allI y φ     => .allI y (φ.substBV b k v)
  | .allB y φ     => .allB y (φ.substBV b k v)

def Refinement.substBV (b : Base) (k : Nat) (v : b.interp)
    {b' : Base} (r : Refinement b') : Refinement b' :=
  match r with
  | .fmla φ       => .fmla (φ.substBV b k v)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, Term.substBV b k v a.2⟩))

/-- Substitute Val `va` for BVar 0 throughout type `t`.
    `substBV_aux` tracks the de Bruijn level as we descend into arrows
    (mirroring `Ty.openVar`'s level-shift in the codomain). -/
def Ty.substBV_aux (k : Nat) (va : Val) : Ty → Ty
  | .refine b r =>
    match va with
    | .iconst n  => .refine b (r.substBV .int  k n)
    | .bconst bv => .refine b (r.substBV .bool k bv)
    | .clos _    => .refine b r
  | .arrow s t => .arrow (s.substBV_aux k va) (t.substBV_aux (k + 1) va)

def Ty.substBV (va : Val) (t : Ty) : Ty := Ty.substBV_aux 0 va t

@[simp]
theorem Ty.skel_substBV (va : Val) (t : Ty) : (t.substBV va).skel = t.skel := by
  simp only [Ty.substBV]
  suffices h : ∀ k, (t.substBV_aux k va).skel = t.skel from h 0
  induction t with
  | refine b r => intro k; cases va <;> simp [Ty.substBV_aux, Ty.skel]
  | arrow s t ihs iht => intro k; simp [Ty.substBV_aux, Ty.skel, ihs, iht]

/-! ### Commutativity of substBV_aux at different levels

  `substBV_aux k va` (substituting bvar at level k) and `substBV_aux j va'`
  (substituting bvar at level j ≠ k) act on disjoint bvar slots and commute.
  Similarly, `openVar j x` (opening bvar at level j) commutes with
  `substBV_aux k va` when j ≠ k.

  These are needed to prove `TyDenote.substBV_iff` for the arrow case,
  where the codomain `t'` has level-(k+1) bvars for the outer binder and
  level-k bvars for the inner binder. -/

/-- `Term.substBV` at different levels commute. -/
private theorem Term.substBV_comm {b'' : Base} (t : Term b'') (b : Base) (k : Nat) (v : b.interp)
    (b' : Base) (j : Nat) (w : b'.interp) (hkj : k ≠ j) :
    Term.substBV b k v (Term.substBV b' j w t) =
    Term.substBV b' j w (Term.substBV b k v t) := by
  induction t with
  | bvar b''' i  =>
    cases b <;>
    cases b' <;>
    cases b''' <;>
    by_cases i = j <;>
    by_cases i = k <;>
    grind [substBV, Ne.symm hkj]
  | _ =>
    cases b <;>
    cases b' <;>
    grind [substBV]

/-- `Formula.substBV` at different levels commute. -/
private theorem Formula.substBV_comm (φ : Formula) (b : Base) (k : Nat) (v : b.interp)
    (b' : Base) (j : Nat) (w : b'.interp) (hkj : k ≠ j) :
    Formula.substBV b k v (Formula.substBV b' j w φ) =
    Formula.substBV b' j w (Formula.substBV b k v φ) := by
  induction φ with
  | tt | ff => simp_all [substBV]
  | eqI | eqB | leqI | and | not | or | imp | exI | exB | allI | allB =>
    cases b <;> cases b' <;> grind [openBVar, substBV, Term.substBV_comm]

/-- `Term.openBVar` at level j and `Term.substBV` at level k ≠ j commute. -/
private theorem Term.openBVar_substBV_comm {b'' : Base} (t : Term b'')
    (b : Base) (j : Nat) (x : EVar)
    (b' : Base) (k : Nat) (v : b'.interp) (hjk : j ≠ k) :
    Term.openBVar b j x (Term.substBV b' k v t) =
    Term.substBV b' k v (Term.openBVar b j x t) := by
  induction t with
  | const b''' c => simp_all [openBVar, substBV]
  | bvar b''' n  => cases b <;> cases b' <;> cases b''' <;> by_cases n = k <;> by_cases n = j <;> simp_all [openBVar, substBV]
  | add | and | not | fvar => cases b <;> cases b' <;> grind [openBVar, substBV]


/-- `Formula.openBVar` at level j and `Formula.substBV` at level k ≠ j commute. -/
private theorem Formula.openBVar_substBV_comm (φ : Formula)
    (b : Base) (j : Nat) (x : EVar)
    (b' : Base) (k : Nat) (v : b'.interp) (hjk : j ≠ k) :
    Formula.openBVar b j x (Formula.substBV b' k v φ) =
    Formula.substBV b' k v (Formula.openBVar b j x φ) := by
  induction φ with
  | tt | ff => simp_all [openBVar, substBV]
  | eqI | eqB | leqI | and | not | or | imp | exI | exB | allI | allB =>
    cases b <;> cases b' <;> grind [openBVar, substBV, Term.openBVar_substBV_comm]

/-- `Refinement.substBV` at different levels commute. -/
theorem Refinement.substBV_comm {b'' : Base} (r : Refinement b'') (b : Base) (k : Nat)
    (v : b.interp) (b' : Base) (j : Nat) (w : b'.interp) (hkj : k ≠ j) :
    Refinement.substBV b k v (Refinement.substBV b' j w r)
      = Refinement.substBV b' j w (Refinement.substBV b k v r) := by
  cases r with
  | fmla φ => simp only [Refinement.substBV]; rw [Formula.substBV_comm φ b k v b' j w hkj]
  | kapp kn args =>
    simp only [Refinement.substBV, List.map_map]
    congr 1; apply List.map_congr_left; intro a _
    simp only [Function.comp_apply]
    congr 1
    rw [Term.substBV_comm a.2 b k v b' j w hkj]

/-- `Refinement.openBVar` at level j and `Refinement.substBV` at level k ≠ j commute. -/
theorem Refinement.openBVar_substBV_comm {b'' : Base} (r : Refinement b'')
    (b : Base) (j : Nat) (x : EVar) (b' : Base) (k : Nat) (v : b'.interp) (hjk : j ≠ k) :
    Refinement.openBVar b j x (Refinement.substBV b' k v r)
      = Refinement.substBV b' k v (Refinement.openBVar b j x r) := by
  cases r with
  | fmla φ => simp only [Refinement.openBVar, Refinement.substBV]
              rw [Formula.openBVar_substBV_comm φ b j x b' k v hjk]
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.substBV, List.map_map]
    congr 1; apply List.map_congr_left; intro a _
    simp only [Function.comp_apply]
    congr 1
    rw [Term.openBVar_substBV_comm a.2 b j x b' k v hjk]

/-- `Ty.openVar` at level j and `Ty.substBV_aux` at level k ≠ j commute. -/
theorem Ty.openVar_substBV_aux_comm (t : Ty) (j : Nat) (x : EVar)
    (va : Val) (k : Nat) (hjk : j ≠ k) :
    (t.substBV_aux k va).openVar j x = (t.openVar j x).substBV_aux k va := by
  induction t generalizing j k  with
  | refine b r =>
    cases va <;> simp_all [openVar, substBV_aux] <;>
    grind [Refinement.openBVar_substBV_comm]
  | arrow s' t' ih1 ih2 =>
    simp_all [openVar, substBV_aux]

/-- `Ty.substBV_aux` at different levels commute. -/
theorem Ty.substBV_aux_comm (t : Ty) (va : Val) (k : Nat) (va' : Val) (j : Nat)
    (hkj : k ≠ j) :
    (t.substBV_aux k va).substBV_aux j va' = (t.substBV_aux j va').substBV_aux k va := by
  induction t generalizing j k  with
  | refine b r =>
    cases va <;> cases va' <;> simp_all [substBV_aux] <;>
    grind [Refinement.substBV_comm]
  | arrow s' t' ih1 ih2 =>
    simp_all [substBV_aux]

/-! ### Well-formedness: BVar base consistency (WFBVarCtx)

  In coq-SystemRF, `WFtype` ensures that bound variables in predicate formulas
  match the base of the enclosing binder's domain type.  In our system, this is
  `Ty.WFBVarCtx ctx t`: for each level `k`, all `BVar b k` in `t`'s refinement
  formulas have `ctx[k]? = some (some b)` (the k-th outer arrow binder's domain base).

  This predicate is required by `TyDenote.substBV_iff` to make `openBVar` of
  the "other" base a provable no-op when the formula is well-formed. -/

/-- `Term.hasBVar b k t`: t contains at least one `Term.bvar b k`. -/
def Term.hasBVar (b : Base) (k : Nat) : {b' : Base} → Term b' → Prop
  | _, .const _ _  => False
  | _, .bvar b' j  => b = b' ∧ k = j
  | _, .fvar _ _   => False
  | _, .add t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | _, .not t      => Term.hasBVar b k t
  | _, .and t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂

/-- `Formula.hasBVar b k φ`: φ contains at least one `Term.bvar b k`. -/
def Formula.hasBVar (b : Base) (k : Nat) : Formula → Prop
  | .tt | .ff => False
  | .eqI t₁ t₂ | .eqB t₁ t₂ | .leqI t₁ t₂ =>
      Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | .and φ₁ φ₂ | .or φ₁ φ₂ | .imp φ₁ φ₂ =>
      Formula.hasBVar b k φ₁ ∨ Formula.hasBVar b k φ₂
  | .not φ | .exI _ φ | .exB _ φ | .allI _ φ | .allB _ φ =>
      Formula.hasBVar b k φ

/-- `Refinement.hasBVar b k r`: r mentions `Term.bvar b k` — in its formula, or
    in the arguments of a κ-application. -/
def Refinement.hasBVar (b : Base) (k : Nat) {b' : Base} (r : Refinement b') : Prop :=
  match r with
  | .fmla φ      => Formula.hasBVar b k φ
  | .kapp _ args => ∃ a ∈ args, Term.hasBVar b k a.2

/-- Extract the base of a refinement type; None for arrow types. -/
def Ty.optBase : Ty → Option Base
  | .refine b _ => some b
  | .arrow _ _  => none

/-- `Ty.WFBVarCtx ctx t`: at nesting depth k, all `BVar b k` in `t`'s
    refinement formulas satisfy `ctx[k]? = some (some b)`.
    `ctx[k]? = some (some b)` means the k-th outer binder has domain base `b`. -/
def Ty.WFBVarCtx : List (Option Base) → Ty → Prop
  | ctx, .refine _ r =>
      ∀ (b : Base) (k : Nat), Refinement.hasBVar b k r → ctx[k]? = some (some b)
  | ctx, .arrow s t  =>
      Ty.WFBVarCtx ctx s ∧ Ty.WFBVarCtx (s.optBase :: ctx) t

/-- Shorthand: `t` is well-formed with no outer binders. -/
def Ty.WFBVars (t : Ty) : Prop := Ty.WFBVarCtx [] t

/-- A typing context is WFBVars iff every binding's type is `Ty.WFBVars` and
    `nuName` is reserved (never used as a binding name). -/
def TEnv.WFBVars (Γ : TEnv) : Prop :=
  (∀ x t, (x, t) ∈ Γ → Ty.WFBVars t) ∧ nuName ∉ Γ.dom

/-- All type annotations syntactically present in `e` are `Ty.WFBVars`.
    Used as a precondition on soundness theorems so the `.ann` case has the
    WFBVars evidence to construct the corresponding `Hastype` node. -/
def Exp.WFBVars : Exp → Prop
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ => True
  | .lam e        => Exp.WFBVars e
  | .letin e₁ e₂  => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .app e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .ann e t      => Ty.WFBVars t ∧ Exp.WFBVars e
  | .and e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .not e        => Exp.WFBVars e
  | .leq e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .ite e₀ e₁ e₂ => Exp.WFBVars e₀ ∧ Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .add e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂

/-- Cons preserves `TEnv.WFBVars` given the new binding has WFBVars type and
    its name is not `nuName`. -/
theorem TEnv.WFBVars.cons {Γ : TEnv} {x : EVar} {t : Ty}
    (hΓ : TEnv.WFBVars Γ) (ht : Ty.WFBVars t) (hxν : x ≠ nuName) :
    TEnv.WFBVars ((x, t) :: Γ) := by
  refine ⟨?_, ?_⟩
  · intro y s h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨_, hst⟩ | h
    · exact hst ▸ ht
    · exact hΓ.1 y s h
  · simp only [TEnv.dom, List.mem_cons, not_or]
    refine ⟨?_, hΓ.2⟩
    intro h; exact hxν h.symm

/-- Lookup in a WFBVars context yields a WFBVars type. -/
theorem TEnv.WFBVars.lookup {Γ : TEnv} (hΓ : TEnv.WFBVars Γ) {x : EVar} {t : Ty}
    (hlk : Γ.lookup x = some t) : Ty.WFBVars t := by
  induction Γ with
  | nil => simp [List.lookup] at hlk
  | cons hd tl ih =>
    obtain ⟨y, s⟩ := hd
    simp only [List.lookup] at hlk
    by_cases hxy : x = y
    · have heq : (x == y) = true := by simp [hxy]
      rw [heq] at hlk
      have hst : s = t := Option.some.inj hlk
      subst hst
      exact hΓ.1 y s (by simp)
    · have hne : (x == y) = false := by simp [hxy]
      rw [hne] at hlk
      have hΓ_tl : TEnv.WFBVars tl := by
        refine ⟨fun z r h => hΓ.1 z r (by simp [List.mem_cons, h]), ?_⟩
        have hnu := hΓ.2
        simp only [TEnv.dom, List.mem_cons, not_or] at hnu
        exact hnu.2
      exact ih hΓ_tl hlk

/-- Lookup in a `nuName`-reserved context never yields `nuName`. -/
theorem TEnv.WFBVars.lookup_ne_nu {Γ : TEnv} (hΓ : TEnv.WFBVars Γ)
    {x : EVar} {t : Ty} (hlk : Γ.lookup x = some t) : x ≠ nuName := by
  intro hxν
  subst hxν
  -- nuName ∈ Γ.dom would contradict hΓ.2
  apply hΓ.2
  -- Derive nuName ∈ Γ.dom from lookup
  induction Γ with
  | nil => simp [List.lookup] at hlk
  | cons hd tl ih =>
    obtain ⟨y, s⟩ := hd
    simp only [List.lookup] at hlk
    simp only [TEnv.dom, List.mem_cons]
    by_cases hxy : nuName = y
    · exact Or.inl hxy
    · right
      have hne : (nuName == y) = false := by simp [hxy]
      rw [hne] at hlk
      have hΓ_tl : TEnv.WFBVars tl := by
        refine ⟨fun z r h => hΓ.1 z r (by simp [List.mem_cons, h]), ?_⟩
        have hnu := hΓ.2
        simp only [TEnv.dom, List.mem_cons, not_or] at hnu
        exact hnu.2
      exact ih hΓ_tl hlk

/-- If t has no `BVar b k`, then `Term.openBVar b k x` is the identity. -/
theorem Term.openBVar_noop (b : Base) (k : Nat) (x : EVar) :
    ∀ {b' : Base} (t : Term b'), ¬Term.hasBVar b k t → Term.openBVar b k x t = t := by
  intro b' t h
  induction t with
  | const _ _ => simp [Term.openBVar]
  | bvar b'' j =>
    simp [Term.hasBVar] at h
    cases b'' <;> cases b <;> simp_all [Term.openBVar, Ne.symm]
  | fvar _ _ => simp [Term.openBVar]
  | add t₁ t₂ ih1 ih2 =>
    simp [Term.hasBVar] at h
    simp [Term.openBVar, ih1 h.1, ih2 h.2]
  | not t ih =>
    simp [Term.hasBVar] at h
    simp [Term.openBVar, ih h]
  | and t₁ t₂ ih1 ih2 =>
    simp [Term.hasBVar] at h
    simp [Term.openBVar, ih1 h.1, ih2 h.2]

/-- If φ has no `BVar b k`, then `openBVar b k x` is the identity. -/
theorem Formula.openBVar_noop (φ : Formula) (b : Base) (k : Nat) (x : EVar)
    (h : ¬Formula.hasBVar b k φ) : φ.openBVar b k x = φ := by
  induction φ with
  | tt | ff => simp [Formula.openBVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar] at h
    simp [Formula.openBVar, Term.openBVar_noop b k x _ h.1, Term.openBVar_noop b k x _ h.2]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar] at h
    simp [Formula.openBVar, ih1 h.1, ih2 h.2]
  | not φ ih | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp [Formula.hasBVar] at h
    simp [Formula.openBVar, ih h]

/-- If t has no `BVar b k`, then `Term.substBV b k v` is the identity. -/
private theorem Term.substBV_noop (b : Base) (k : Nat) (v : b.interp) :
    ∀ {b' : Base} (t : Term b'), ¬Term.hasBVar b k t → Term.substBV b k v t = t := by
  intro b' t h
  induction t with
  | const _ _ => simp [Term.substBV]
  | bvar b'' j =>
    simp [Term.hasBVar] at h
    cases b'' <;> cases b <;> simp_all [Term.substBV, Ne.symm]
  | fvar _ _ => simp [Term.substBV]
  | add t₁ t₂ ih1 ih2 =>
    simp [Term.hasBVar] at h; simp [Term.substBV, ih1 h.1, ih2 h.2]
  | not t ih =>
    simp [Term.hasBVar] at h; simp [Term.substBV, ih h]
  | and t₁ t₂ ih1 ih2 =>
    simp [Term.hasBVar] at h; simp [Term.substBV, ih1 h.1, ih2 h.2]

/-- If φ has no `BVar b k`, then `substBV b k v` is the identity. -/
theorem Formula.substBV_noop (φ : Formula) (b : Base) (k : Nat) (v : b.interp)
    (h : ¬Formula.hasBVar b k φ) : φ.substBV b k v = φ := by
  induction φ with
  | tt | ff => simp [Formula.substBV]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar] at h
    simp [Formula.substBV, Term.substBV_noop b k v _ h.1, Term.substBV_noop b k v _ h.2]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar] at h; simp [Formula.substBV, ih1 h.1, ih2 h.2]
  | not φ ih | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp [Formula.hasBVar] at h; simp [Formula.substBV, ih h]

/-- WFBVarCtx ensures that a BVar of the "wrong" base (≠ context base) can't appear,
    so `openBVar` of that wrong base at level 0 is a no-op. -/
theorem Formula.openBVar_noop_wf (φ : Formula) (b b_d : Base) (hne : b ≠ b_d)
    (ctx : List (Option Base)) (x : EVar)
    (hWF : ∀ (b' : Base) (k : Nat), Formula.hasBVar b' k φ → ctx[k]? = some (some b'))
    (hctx : ctx[0]? = some (some b_d)) :
    φ.openBVar b 0 x = φ := by
  apply Formula.openBVar_noop
  intro hbv
  have := hWF b 0 hbv
  rw [hctx] at this
  exact hne (by simp_all)

/-- Opening a term at (b, k) eliminates all BVar b k occurrences. -/
private theorem Term.not_hasBVar_openBVar_same (b : Base) (k : Nat) (x : EVar) :
    ∀ {b' : Base} (t : Term b'), ¬Term.hasBVar b k (Term.openBVar b k x t) := by
  intro b' t
  induction t with
  | const _ _ => simp [Term.openBVar, Term.hasBVar]
  | bvar b'' j =>
    cases b'' <;> cases b <;> simp_all [Term.openBVar, Term.hasBVar]
      <;> by_cases j = k <;> grind [Term.openBVar, Term.hasBVar]
  | fvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | add t₁ t₂ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]
  | not t ih  => simp [Term.openBVar, Term.hasBVar, ih]
  | and t₁ t₂ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]

/-- Opening at (b', j) preserves hasBVar b k when (b, k) ≠ (b', j). -/
private theorem Term.hasBVar_openBVar_other {b'' : Base} (t : Term b'')
    (b b' : Base) (k j : Nat) (x : EVar) (hne : b ≠ b' ∨ k ≠ j) :
    Term.hasBVar b k (Term.openBVar b' j x t) ↔ Term.hasBVar b k t := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.hasBVar]
  | bvar b'' i =>
    cases b'' <;> cases b <;> cases b' <;> simp_all [Term.openBVar, Term.hasBVar] <;> grind [hasBVar]
  | fvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | add _ _ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]
  | not _ ih  => simp [Term.openBVar, Term.hasBVar, ih]
  | and _ _ ih1 ih2 => simp [Term.openBVar, Term.hasBVar, ih1, ih2]

/-- Opening φ at (b, k) eliminates all hasBVar b k. -/
theorem Formula.not_hasBVar_openBVar_same (φ : Formula) (b : Base) (k : Nat) (x : EVar) :
    ¬Formula.hasBVar b k (φ.openBVar b k x) := by
  induction φ with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar, Formula.openBVar, Term.not_hasBVar_openBVar_same]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar, Formula.openBVar, ih1, ih2]
  | not φ ih | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp [Formula.hasBVar, Formula.openBVar, ih]

/-- Opening φ at (b', j) with (b, k) ≠ (b', j) preserves hasBVar b k. -/
theorem Formula.hasBVar_openBVar_other (φ : Formula) (b b' : Base) (k j : Nat) (x : EVar)
    (hne : b ≠ b' ∨ k ≠ j) :
    Formula.hasBVar b k (φ.openBVar b' j x) ↔ Formula.hasBVar b k φ := by
  induction φ with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.hasBVar, Formula.openBVar,
          Term.hasBVar_openBVar_other _ b b' k j x hne]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp [Formula.hasBVar, Formula.openBVar, ih1, ih2]
  | not φ ih | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp [Formula.hasBVar, Formula.openBVar, ih]

/-! Refinement-level analogues of the `Formula.*` openBVar BVar lemmas: case-split
    the enum and dispatch κ-application arguments via the `Term.*` lemmas. -/

theorem Refinement.not_hasBVar_openBVar_same {b'' : Base} (r : Refinement b'')
    (b : Base) (k : Nat) (x : EVar) : ¬Refinement.hasBVar b k (r.openBVar b k x) := by
  cases r with
  | fmla φ => exact Formula.not_hasBVar_openBVar_same φ b k x
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar]
    rintro ⟨a, hmem, hbv⟩
    simp only [List.mem_map] at hmem
    obtain ⟨a', _, rfl⟩ := hmem
    exact Term.not_hasBVar_openBVar_same b k x a'.2 hbv

theorem Refinement.hasBVar_openBVar_other {b'' : Base} (r : Refinement b'')
    (b b' : Base) (k j : Nat) (x : EVar) (hne : b ≠ b' ∨ k ≠ j) :
    Refinement.hasBVar b k (r.openBVar b' j x) ↔ Refinement.hasBVar b k r := by
  cases r with
  | fmla φ => exact Formula.hasBVar_openBVar_other φ b b' k j x hne
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar]
    constructor
    · rintro ⟨a, hmem, hbv⟩
      simp only [List.mem_map] at hmem
      obtain ⟨a', hmem', rfl⟩ := hmem
      exact ⟨a', hmem', (Term.hasBVar_openBVar_other a'.2 b b' k j x hne).mp hbv⟩
    · rintro ⟨a, hmem, hbv⟩
      exact ⟨⟨a.1, Term.openBVar b' j x a.2⟩,
             by simp only [List.mem_map]; exact ⟨a, hmem, rfl⟩,
             (Term.hasBVar_openBVar_other a.2 b b' k j x hne).mpr hbv⟩

/-- Refinement-level `openBVar_noop`: opening at a base/level with no occurrence
    is the identity. -/
theorem Refinement.openBVar_noop {b' : Base} (r : Refinement b') (b : Base) (k : Nat)
    (x : EVar) (h : ¬Refinement.hasBVar b k r) : Refinement.openBVar b k x r = r := by
  cases r with
  | fmla φ =>
    simp only [Refinement.openBVar]
    rw [Formula.openBVar_noop φ b k x (by simpa [Refinement.hasBVar] using h)]
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar] at h ⊢
    congr 1
    have hmap : ∀ a ∈ args,
        (fun a => (⟨a.1, Term.openBVar b k x a.2⟩ : Σ b : Base, Term b)) a = id a := by
      intro a ha
      simp only [id]; congr 1
      exact Term.openBVar_noop b k x a.2 (fun hbv => h ⟨a, ha, hbv⟩)
    simp [List.map_congr_left hmap]

/-- `optBase` is unchanged by `openVar` (shape refine/arrow is preserved). -/
theorem Ty.optBase_openVar (t : Ty) (k : Nat) (y : EVar) :
    (t.openVar k y).optBase = t.optBase := by
  cases t <;> simp [Ty.openVar, Ty.optBase]

/-- Opening at level `ctx.length` (the last binder position) consumes the last
    context entry. For the `app` case use ctx = [], opt = s.optBase:
    `WFBVarCtx [s.optBase] t → WFBVarCtx [] (t.openVar 0 y)`. -/
theorem Ty.WFBVarCtx_openVar_last (t : Ty) (ctx : List (Option Base)) (opt : Option Base)
    (y : EVar) (hWF : Ty.WFBVarCtx (ctx ++ [opt]) t) :
    Ty.WFBVarCtx ctx (t.openVar ctx.length y) := by
  induction t generalizing ctx with
  | refine b r =>
    simp only [Ty.openVar, Ty.WFBVarCtx] at hWF ⊢
    intro b' k hbv
    -- Strip the two openBVar applications to get hasBVar on the original r.
    by_cases hklen : k = ctx.length
    · -- k = ctx.length: this is the opened level — no BVar survives
      subst hklen
      cases b' with
      | int =>
        have hno : ¬Refinement.hasBVar .int ctx.length
            ((r.openBVar .int ctx.length y).openBVar .bool ctx.length y) := by
          rw [Refinement.hasBVar_openBVar_other _ .int .bool ctx.length ctx.length y
                (Or.inl (by decide))]
          exact Refinement.not_hasBVar_openBVar_same _ .int ctx.length y
        exact absurd hbv hno
      | bool =>
        exact absurd hbv (Refinement.not_hasBVar_openBVar_same _ .bool ctx.length y)
    · -- k ≠ ctx.length: BVar k survived both openings → it was in original r.
      have hbv' : Refinement.hasBVar b' k r := by
        rw [Refinement.hasBVar_openBVar_other _ _ _ _ _ _ (Or.inr hklen),
            Refinement.hasBVar_openBVar_other _ _ _ _ _ _ (Or.inr hklen)] at hbv
        exact hbv
      have hWF' := hWF b' k hbv'
      -- Extract ctx[k]? from (ctx ++ [opt])[k]?
      simp only [List.getElem?_append] at hWF'
      by_cases hklt : k < ctx.length
      · simp [hklt] at hWF' ⊢; exact hWF'
      · have hkge : ctx.length ≤ k := Nat.le_of_not_lt hklt
        have hkgt : ctx.length < k := Nat.lt_of_le_of_ne hkge (Ne.symm hklen)
        simp [Nat.not_lt.mpr hkge] at hWF'
        grind
  | arrow s t ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.openVar]
    refine ⟨ihs ctx hWF.1, ?_⟩
    -- Codomain uses IH with ctx' = s.optBase :: ctx
    have ih := iht (s.optBase :: ctx) (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih

-- Helpers for WFBVarCtx_substBV_aux_last

private theorem Term.not_hasBVar_substBV_same {b' : Base} (t : Term b') (b : Base) (k : Nat)
    (v : b.interp) : ¬Term.hasBVar b k (Term.substBV b k v t) := by
  induction t with
  | const _ _ => simp [Term.hasBVar, Term.substBV]
  | bvar b'' j => cases b <;> cases b'' <;> grind [Term.substBV, Term.hasBVar]
  | fvar _ _ => simp [Term.hasBVar, Term.substBV]
  | add t₁ t₂ ih1 ih2 =>
    simp only [Term.hasBVar, Term.substBV, not_or]; exact ⟨ih1, ih2⟩
  | not t ih => simp [Term.hasBVar, Term.substBV, ih]
  | and t₁ t₂ ih1 ih2 =>
    simp only [Term.hasBVar, Term.substBV, not_or]; exact ⟨ih1, ih2⟩

private theorem Formula.not_hasBVar_substBV_same (b : Base) (k : Nat) (v : b.interp)
    (φ : Formula) : ¬Formula.hasBVar b k (φ.substBV b k v) := by
  induction φ with
  | tt | ff => simp [Formula.hasBVar, Formula.substBV]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.substBV, Formula.hasBVar, not_or]
    exact ⟨Term.not_hasBVar_substBV_same _ b k v, Term.not_hasBVar_substBV_same _ b k v⟩
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp only [Formula.substBV, Formula.hasBVar, not_or]; exact ⟨ih1, ih2⟩
  | not φ ih | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp [Formula.substBV, Formula.hasBVar, ih]

private theorem Term.hasBVar_substBV_mono {b'' : Base} (t : Term b'') (b b' : Base) (k j : Nat)
    (v : b'.interp) (h : Term.hasBVar b k (Term.substBV b' j v t)) : Term.hasBVar b k t := by
  induction t with
  | const _ _ => simp [Term.hasBVar, Term.substBV] at h
  | bvar b''' i =>
    cases b' <;> cases b''' <;> grind [Term.substBV, Term.hasBVar]
  | fvar _ _ => simp [Term.hasBVar, Term.substBV] at h
  | add t₁ t₂ ih1 ih2 =>
    simp only [Term.hasBVar, Term.substBV] at h ⊢
    rcases h with h | h
    · left; exact ih1 h
    · right; exact ih2 h
  | not t ih =>
    simp only [Term.hasBVar, Term.substBV] at h ⊢; exact ih h
  | and t₁ t₂ ih1 ih2 =>
    simp only [Term.hasBVar, Term.substBV] at h ⊢
    rcases h with h | h
    · left; exact ih1 h
    · right; exact ih2 h

private theorem Formula.hasBVar_substBV_mono {b b' : Base} {k j : Nat} {v : b'.interp}
    {φ : Formula} (h : Formula.hasBVar b k (φ.substBV b' j v)) : Formula.hasBVar b k φ := by
  induction φ with
  | tt | ff => simp [Formula.hasBVar, Formula.substBV] at h
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.substBV, Formula.hasBVar] at h ⊢
    rcases h with h | h
    · left;  exact Term.hasBVar_substBV_mono _ b b' k j v h
    · right; exact Term.hasBVar_substBV_mono _ b b' k j v h
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp only [Formula.substBV, Formula.hasBVar] at h ⊢
    rcases h with h | h
    · left; exact ih1 h
    · right; exact ih2 h
  | not φ ih | exI _ φ ih | exB _ φ ih | allI _ φ ih | allB _ φ ih =>
    simp only [Formula.substBV, Formula.hasBVar] at h ⊢; exact ih h

/-- Refinement-level analogues of the `Formula.*` substBV BVar lemmas. -/
theorem Refinement.not_hasBVar_substBV_same {b'' : Base} (b : Base) (k : Nat)
    (v : b.interp) (r : Refinement b'') : ¬Refinement.hasBVar b k (r.substBV b k v) := by
  cases r with
  | fmla φ => exact Formula.not_hasBVar_substBV_same b k v φ
  | kapp kn args =>
    simp only [Refinement.substBV, Refinement.hasBVar]
    rintro ⟨a, hmem, hbv⟩
    simp only [List.mem_map] at hmem
    obtain ⟨a', _, rfl⟩ := hmem
    exact Term.not_hasBVar_substBV_same a'.2 b k v hbv

theorem Refinement.hasBVar_substBV_mono {b'' : Base} {b b' : Base} {k j : Nat}
    {v : b'.interp} {r : Refinement b''}
    (h : Refinement.hasBVar b k (r.substBV b' j v)) : Refinement.hasBVar b k r := by
  cases r with
  | fmla φ => exact Formula.hasBVar_substBV_mono h
  | kapp kn args =>
    simp only [Refinement.substBV, Refinement.hasBVar] at h ⊢
    obtain ⟨a, hmem, hbv⟩ := h
    simp only [List.mem_map] at hmem
    obtain ⟨a', hmem', rfl⟩ := hmem
    exact ⟨a', hmem', Term.hasBVar_substBV_mono a'.2 b b' k j v hbv⟩

private theorem Ty.optBase_substBV_aux (t : Ty) (k : Nat) (va : Val) :
    (t.substBV_aux k va).optBase = t.optBase := by
  cases t with
  | refine b r => cases va <;> simp [Ty.substBV_aux, Ty.optBase]
  | arrow s' t' => simp [Ty.substBV_aux, Ty.optBase]

/-- For k > ctx.length, both (ctx ++ [opt])[k]? and (ctx ++ [none])[k]? are none. -/
private theorem List.getElem?_append_singleton_gt (opt : α) (ctx : List α) (k : Nat)
    (hgt : ctx.length < k) : (ctx ++ [opt])[k]? = none := by
  rw [List.getElem?_eq_none_iff]
  simp; omega

/-- WFBVarCtx is preserved by substBV_aux at the last (ctx.length-th) slot:
    the slot changes from `opt` to `none` (since the BVar at that level is consumed). -/
theorem Ty.WFBVarCtx_substBV_aux_last (t : Ty) (ctx : List (Option Base))
    (opt : Option Base) (va : Val)
    (hWF : Ty.WFBVarCtx (ctx ++ [opt]) t)
    (hcompat_int  : opt = some .int  → ∃ n,  va = .iconst n)
    (hcompat_bool : opt = some .bool → ∃ bv, va = .bconst bv) :
    Ty.WFBVarCtx (ctx ++ [none]) (t.substBV_aux ctx.length va) := by
  induction t generalizing ctx with
  | refine b r =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.substBV_aux]
    -- Helper: for k ≠ ctx.length, (ctx ++ [opt])[k]? = (ctx ++ [none])[k]?
    have ctx_agree : ∀ k, k ≠ ctx.length → (ctx ++ [opt])[k]? = (ctx ++ [none])[k]? := by
      intro k hk
      by_cases hlt : k < ctx.length
      · simp [List.getElem?_append, hlt]
      · have hge : ctx.length ≤ k := Nat.le_of_not_lt hlt
        have hgt : ctx.length < k := Nat.lt_of_le_of_ne hge (Ne.symm hk)
        simp [List.getElem?_append_singleton_gt opt ctx k hgt,
              List.getElem?_append_singleton_gt none ctx k hgt]
    -- Helper: (ctx ++ [opt])[ctx.length]? = opt
    have ctx_last : (ctx ++ [opt])[ctx.length]? = some opt := by
      simp
    cases va with
    | clos _ =>
      intro b' k hbv
      have hctx := hWF b' k hbv
      by_cases hk : k = ctx.length
      · subst hk
        rw [ctx_last] at hctx
        -- hctx : some opt = some (some b')
        have hopt : opt = some b' := Option.some.inj hctx
        exfalso
        cases opt with
        | none => simp at hopt
        | some ob =>
          cases ob with
          | int  => obtain ⟨n, hn⟩ := hcompat_int rfl; simp at hn
          | bool => obtain ⟨bv, hbv'⟩ := hcompat_bool rfl; simp at hbv'
      · rw [← ctx_agree k hk]; exact hctx
    | iconst n =>
      intro b' k hbv
      have hbv_orig := Refinement.hasBVar_substBV_mono hbv
      have hctx := hWF b' k hbv_orig
      by_cases hk : k = ctx.length
      · subst hk
        exfalso
        cases b' with
        | int  => exact Refinement.not_hasBVar_substBV_same .int ctx.length n r hbv
        | bool =>
          rw [ctx_last] at hctx
          have hopt : opt = some .bool := Option.some.inj hctx
          obtain ⟨bv, hbv'⟩ := hcompat_bool hopt
          simp at hbv'
      · rw [← ctx_agree k hk]; exact hctx
    | bconst bv =>
      intro b' k hbv
      have hbv_orig := Refinement.hasBVar_substBV_mono hbv
      have hctx := hWF b' k hbv_orig
      by_cases hk : k = ctx.length
      · subst hk
        exfalso
        cases b' with
        | bool => exact Refinement.not_hasBVar_substBV_same .bool ctx.length bv r hbv
        | int  =>
          rw [ctx_last] at hctx
          have hopt : opt = some .int := Option.some.inj hctx
          obtain ⟨n, hn⟩ := hcompat_int hopt
          simp at hn
      · rw [← ctx_agree k hk]; exact hctx
  | arrow s' t' ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.substBV_aux]
    refine ⟨ihs ctx hWF.1, ?_⟩
    -- Codomain: apply iht with ctx' = s'.optBase :: ctx
    have ih := iht (s'.optBase :: ctx) hWF.2
    simp only [List.length_cons] at ih
    rw [Ty.optBase_substBV_aux, ← List.cons_append]
    exact ih

/-- For k ≠ ctx.length, replacing the element at ctx.length doesn't affect index k. -/
private theorem optBase_list_getElem?_update_middle (ctx : List (Option Base)) (a b : Option Base)
    (rest : List (Option Base)) (k : Nat) (hk : k ≠ ctx.length) :
    (ctx ++ [a] ++ rest)[k]? = (ctx ++ [b] ++ rest)[k]? := by
  induction ctx generalizing k with
  | nil =>
    simp only [List.nil_append, List.length_nil] at hk ⊢
    rcases k with _ | k
    · exact absurd rfl hk
    · simp [List.getElem?_cons_succ]
  | cons hd tl ih =>
    simp only [List.cons_append, List.length_cons] at hk ⊢
    rcases k with _ | k
    · rfl
    · simp only [List.getElem?_cons_succ]
      exact ih _ (by omega)

/-- The element at ctx.length in ctx ++ [a] ++ rest is some a. -/
private theorem optBase_list_getElem?_middle (ctx : List (Option Base)) (a : Option Base)
    (rest : List (Option Base)) :
    (ctx ++ [a] ++ rest)[ctx.length]? = some a := by
  induction ctx with
  | nil => simp
  | cons hd tl ih => simp

/-- Generalization of `WFBVarCtx_substBV_aux_last` allowing extra context after the slot.
    WFBVarCtx is preserved by substBV_aux at slot `ctx.length`, with `rest` unchanged. -/
theorem Ty.WFBVarCtx_substBV_aux_prefix (t : Ty) (ctx : List (Option Base))
    (opt : Option Base) (rest : List (Option Base)) (va : Val)
    (hWF : Ty.WFBVarCtx (ctx ++ [opt] ++ rest) t)
    (hcompat_int  : opt = some .int  → ∃ n,  va = .iconst n)
    (hcompat_bool : opt = some .bool → ∃ bv, va = .bconst bv) :
    Ty.WFBVarCtx (ctx ++ [none] ++ rest) (t.substBV_aux ctx.length va) := by
  induction t generalizing ctx with
  | refine b r =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.substBV_aux]
    have ctx_last := optBase_list_getElem?_middle ctx opt rest
    cases va with
    | clos _ =>
      intro b' k hbv
      have hctx := hWF b' k hbv
      by_cases hk : k = ctx.length
      · subst hk
        rw [ctx_last] at hctx
        have hopt : opt = some b' := Option.some.inj hctx
        exfalso
        cases opt with
        | none => simp at hopt
        | some ob =>
          cases ob with
          | int  => obtain ⟨n, hn⟩ := hcompat_int rfl; simp at hn
          | bool => obtain ⟨bv, hbv'⟩ := hcompat_bool rfl; simp at hbv'
      · rw [← optBase_list_getElem?_update_middle ctx opt none rest k hk]; exact hctx
    | iconst n =>
      intro b' k hbv
      have hbv_orig := Refinement.hasBVar_substBV_mono hbv
      have hctx := hWF b' k hbv_orig
      by_cases hk : k = ctx.length
      · subst hk
        exfalso
        cases b' with
        | int  => exact Refinement.not_hasBVar_substBV_same .int ctx.length n r hbv
        | bool =>
          rw [ctx_last] at hctx
          have hopt : opt = some .bool := Option.some.inj hctx
          obtain ⟨bv, hbv'⟩ := hcompat_bool hopt
          simp at hbv'
      · rw [← optBase_list_getElem?_update_middle ctx opt none rest k hk]; exact hctx
    | bconst bv =>
      intro b' k hbv
      have hbv_orig := Refinement.hasBVar_substBV_mono hbv
      have hctx := hWF b' k hbv_orig
      by_cases hk : k = ctx.length
      · subst hk
        exfalso
        cases b' with
        | bool => exact Refinement.not_hasBVar_substBV_same .bool ctx.length bv r hbv
        | int  =>
          rw [ctx_last] at hctx
          have hopt : opt = some .int := Option.some.inj hctx
          obtain ⟨n, hn⟩ := hcompat_int hopt
          simp at hn
      · rw [← optBase_list_getElem?_update_middle ctx opt none rest k hk]; exact hctx
  | arrow s' t' ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.substBV_aux]
    refine ⟨ihs ctx hWF.1, ?_⟩
    have ih := iht (s'.optBase :: ctx) hWF.2
    simp only [List.length_cons] at ih
    rw [Ty.optBase_substBV_aux, ← List.cons_append]
    exact ih

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

/-! ## 8. Closing substitution (for big-step / fundamental lemma) -/

/-- Closing substitution driven by the runtime environment `ρ`. Since `ρ` is a
    *total* function `EVar → Val`, this is a structural *simultaneous* value
    substitution: every free name `x` is replaced by `(ρ.map x).toExp`. No domain
    is needed — on a well-typed term every free name is bound in the model, and
    the `iconst 0` default never occurs at a name that is actually read.

    This is exactly the merge of the old list-based closing substitution `γ` with
    the refinement environment `ρ`: `ρ` *is* `γ`. -/
def Exp.substEnv (ρ : REnv) : Exp → Exp
  | .bvar j       => .bvar j
  | .fvar x       => (ρ.map x).toExp
  | .iconst n     => .iconst n
  | .bconst b     => .bconst b
  | .lam body     => .lam (Exp.substEnv ρ body)
  | .letin e₁ e₂  => .letin (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂)
  | .app e₁ e₂    => .app (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂)
  | .ann e t      => .ann (Exp.substEnv ρ e) t
  | .add e₁ e₂    => .add (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂)
  | .leq e₁ e₂    => .leq (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂)
  | .not e        => .not (Exp.substEnv ρ e)
  | .and e₁ e₂    => .and (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂)
  | .ite e₀ e₁ e₂ => .ite (Exp.substEnv ρ e₀) (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂)

/-! ## 9. Freshness helper

  `EVar.fresh L` returns a name not in `L`, by producing a string longer than
  any element of `L`. The freshness proof lives in Stage 2b. -/

def EVar.maxLen : List EVar → Nat
  | []      => 0
  | x :: xs => Nat.max x.length (EVar.maxLen xs)

def EVar.fresh (L : List EVar) : EVar :=
  String.ofList (List.replicate (EVar.maxLen L + 1) 'x')

/-! ## 10. REnv helpers -/

/-- Updating cell `x` leaves a *different* cell `y` untouched — for any bases,
    since `update` only writes cell `x`. -/
theorem REnv.map_update_other (b : Base) (ρ : REnv) (x : EVar) (v : b.interp)
    {y : EVar} (h : x ≠ y) : (ρ.update b x v).map y = ρ.map y := by
  have hxy : (x == y) = false := by simp [h]
  simp [hxy]

@[simp] theorem REnv.get_update_same (b : Base) (ρ : REnv) (x : EVar) (v : b.interp) :
    REnv.get b (ρ.update b x v) x = v := by
  cases b <;> simp [REnv.get]

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

/-! ## 15. `Exp.substEnv` push-through lemmas

  Under the structural definition each constructor case is *definitional*
  (`rfl`); the lemmas are kept (as `@[simp]`) so existing call sites and the
  `simp` set continue to fire by name. -/

@[simp]
theorem Exp.substEnv_fvar (ρ : REnv) (x : EVar) :
    Exp.substEnv ρ (.fvar x) = (ρ.map x).toExp := rfl

@[simp]
theorem Exp.substEnv_iconst (ρ : REnv) (n : Int) :
    Exp.substEnv ρ (.iconst n) = .iconst n := rfl

@[simp]
theorem Exp.substEnv_bconst (ρ : REnv) (b : Bool) :
    Exp.substEnv ρ (.bconst b) = .bconst b := rfl

@[simp]
theorem Exp.substEnv_bvar (ρ : REnv) (j : Nat) :
    Exp.substEnv ρ (.bvar j) = .bvar j := rfl

@[simp]
theorem Exp.substEnv_lam (ρ : REnv) (body : Exp) :
    Exp.substEnv ρ (.lam body) = .lam (Exp.substEnv ρ body) := rfl

@[simp]
theorem Exp.substEnv_letin (ρ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv ρ (.letin e₁ e₂) = .letin (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂) := rfl

@[simp]
theorem Exp.substEnv_app (ρ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv ρ (.app e₁ e₂) = .app (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂) := rfl

@[simp]
theorem Exp.substEnv_ann (ρ : REnv) (e : Exp) (t : Ty) :
    Exp.substEnv ρ (.ann e t) = .ann (Exp.substEnv ρ e) t := rfl

@[simp]
theorem Exp.substEnv_add (ρ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv ρ (.add e₁ e₂) = .add (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂) := rfl

@[simp]
theorem Exp.substEnv_leq (ρ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv ρ (.leq e₁ e₂) = .leq (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂) := rfl

@[simp]
theorem Exp.substEnv_not (ρ : REnv) (e : Exp) :
    Exp.substEnv ρ (.not e) = .not (Exp.substEnv ρ e) := rfl

@[simp]
theorem Exp.substEnv_and (ρ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv ρ (.and e₁ e₂) = .and (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂) := rfl

@[simp]
theorem Exp.substEnv_ite (ρ : REnv) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv ρ (.ite e₀ e₁ e₂) = .ite (Exp.substEnv ρ e₀) (Exp.substEnv ρ e₁) (Exp.substEnv ρ e₂) := rfl

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

/-- A closed expression is fixed under the closing substitution. -/
theorem Exp.substEnv_closed (ρ : REnv) (e : Exp) (he : e.fv = []) :
    Exp.substEnv ρ e = e := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar y => simp [Exp.fv] at he
  | lam body ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | ann e t ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | not e ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.append_eq_nil_iff] at he
    simp only [Exp.substEnv, ih₁ he.1, ih₂ he.2]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.append_eq_nil_iff] at he
    simp only [Exp.substEnv, ih₀ he.1.1, ih₁ he.1.2, ih₂ he.2]

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

/-- If every free name of `e` is mapped to a closed value by `ρ`, then the
    closing substitution produces a closed expression. -/
theorem Exp.substEnv_fv_nil (ρ : REnv) (e : Exp)
    (hcl : ∀ z ∈ e.fv, Val.closed (ρ.map z)) :
    (Exp.substEnv ρ e).fv = [] := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar x => exact Val.toExp_closed_of_closed (hcl x (by simp [Exp.fv]))
  | lam body ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | ann e t ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | not e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨ih₁ fun z hz => hcl z (by simp [Exp.fv, hz]),
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨⟨ih₀ fun z hz => hcl z (by simp [Exp.fv, hz]),
            ih₁ fun z hz => hcl z (by simp [Exp.fv, hz])⟩,
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩

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


theorem Ty.lc_at_mono (t : Ty) {j k : Nat} (hjk : j ≤ k) (h : Ty.lc_at j t) :
  Ty.lc_at k t := by
  induction t generalizing j k with
  | refine b r =>
    cases r with
    | fmla φ =>
      simp only [lc_at, Refinement.lc_at] at *
      exact Formula.lc_at_mono φ hjk h
    | kapp kn args =>
      simp only [lc_at, Refinement.lc_at] at *
      intro a hae
      exact Term.lc_at_mono a.snd hjk (h a hae)
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

theorem Exp.substEnv_lc_at (ρ : REnv) (e : Exp) (k : Nat)
    (hρ : ∀ z ∈ e.fv, Val.lc (ρ.map z)) (hlc_e : e.lc_at k) :
    (e.substEnv ρ).lc_at k := by
  induction e generalizing k with
  | bvar j => simpa [Exp.substEnv] using hlc_e
  | iconst _ | bconst _ => trivial
  | fvar x =>
    exact Exp.lc_at_mono _ (Nat.zero_le k) (Val.toExp_lc_at_zero (hρ x (by simp [Exp.fv])))
  | lam body ih =>
    exact ih (k+1) (fun z hz => hρ z (by simpa [Exp.fv] using hz)) hlc_e
  | ann e t ih =>
    exact ih k (fun z hz => hρ z (by simpa [Exp.fv] using hz)) hlc_e
  | not e ih =>
    exact ih k (fun z hz => hρ z (by simpa [Exp.fv] using hz)) hlc_e
  | letin e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hρ z (by simp [Exp.fv, hz])) h₁,
           ih₂ (k+1) (fun z hz => hρ z (by simp [Exp.fv, hz])) h₂⟩
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hρ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hρ z (by simp [Exp.fv, hz])) h₂⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    obtain ⟨h₀, h₁, h₂⟩ := hlc_e
    exact ⟨ih₀ k (fun z hz => hρ z (by simp [Exp.fv, hz])) h₀,
           ih₁ k (fun z hz => hρ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hρ z (by simp [Exp.fv, hz])) h₂⟩

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

/-! ## 19. substEnv-openVal: key lemma for lam/letin cases -/

theorem REnv.write_self (ρ : REnv) (x : EVar) (v : Val) : (ρ.write x v).map x = v := by
  simp

theorem REnv.write_other (ρ : REnv) (x : EVar) (v : Val) {y : EVar} (h : x ≠ y) :
    (ρ.write x v).map y = ρ.map y := by
  have hxy : (x == y) = false := by simp [h]
  simp [hxy]

/-- Writing a cell's current value back is the identity (no `HasBase` needed,
    since `write` is lossless). Drives the simplified `app` case of the
    fundamental lemma. -/
theorem REnv.write_idem (ρ : REnv) (x : EVar) : ρ.write x (ρ.map x) = ρ := by
  apply REnv.ext; funext y
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- The closing substitution depends only on `ρ` over the free names of `e`. -/
theorem Exp.substEnv_congr (e : Exp) (ρ₁ ρ₂ : REnv)
    (h : ∀ z ∈ e.fv, ρ₁.map z = ρ₂.map z) :
    Exp.substEnv ρ₁ e = Exp.substEnv ρ₂ e := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar x => simp only [Exp.substEnv, h x (by simp [Exp.fv])]
  | lam e ih | ann e _ ih | not e ih =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simpa [Exp.fv] using hz)]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₀ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]

/-- Extending `ρ` at a name `y` not free in `e` does not change `substEnv`. The
    single-env analogue of the old `substEnv_cons_fresh`. -/
theorem Exp.substEnv_write_fresh (e : Exp) (ρ : REnv) (y : EVar) (v : Val)
    (h : y ∉ e.fv) :
    Exp.substEnv (ρ.write y v) e = Exp.substEnv ρ e := by
  apply Exp.substEnv_congr
  intro z hz
  exact REnv.write_other ρ y v (by rintro rfl; exact h hz)

/-- Key lemma for the lam/letin cases: opening the binder with a fresh `z` and
    then closing under `ρ.write z va` equals closing the body under `ρ` and then
    plugging `va` into the bound position. The merged single-env analogue of the
    old `substEnv_cons_openVar`. -/
theorem Exp.substEnv_write_openVar (e : Exp) (ρ : REnv) (va : Val) (z : EVar) (k : Nat)
    (hz_fv : z ∉ e.fv) (hρ : ∀ w ∈ e.fv, Val.lc (ρ.map w)) :
    Exp.substEnv (ρ.write z va) (Exp.openVar k z e) =
      Exp.openExp k va.toExp (Exp.substEnv ρ e) := by
  induction e generalizing k with
  | bvar j =>
    by_cases hjk : j = k
    · subst hjk; simp [Exp.openVar, Exp.substEnv, Exp.openExp]
    · simp [Exp.openVar, Exp.substEnv, Exp.openExp, hjk]
  | iconst _ | bconst _ => rfl
  | fvar y =>
    have hyz : z ≠ y := fun he => hz_fv (by simp [Exp.fv, he])
    show Exp.substEnv (ρ.write z va) (.fvar y) = Exp.openExp k va.toExp ((ρ.map y).toExp)
    rw [Exp.substEnv_fvar, REnv.write_other ρ z va hyz]
    exact (Exp.openExp_of_lc_at _ k va.toExp
      (Exp.lc_at_mono _ (Nat.zero_le k)
        (Val.toExp_lc_at_zero (hρ y (by simp [Exp.fv]))))).symm
  | lam e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih (k+1) (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hρ w (by simpa [Exp.fv] using hw))]
  | ann e t ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hρ w (by simpa [Exp.fv] using hw))]
  | not e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hρ w (by simpa [Exp.fv] using hw))]
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hρ w (by simp [Exp.fv, hw])),
      ih₂ (k+1) hz_fv.2 (fun w hw => hρ w (by simp [Exp.fv, hw]))]
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hρ w (by simp [Exp.fv, hw])),
      ih₂ k hz_fv.2 (fun w hw => hρ w (by simp [Exp.fv, hw]))]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    obtain ⟨⟨hz₀, hz₁⟩, hz₂⟩ := hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₀ k hz₀ (fun w hw => hρ w (by simp [Exp.fv, hw])),
      ih₁ k hz₁ (fun w hw => hρ w (by simp [Exp.fv, hw])),
      ih₂ k hz₂ (fun w hw => hρ w (by simp [Exp.fv, hw]))]

/-- Substituting a variable that does not occur free is the identity. -/
theorem Exp.subst_fresh (x : EVar) (u e : Exp) (h : x ∉ e.fv) :
    Exp.subst x u e = e := by
  induction e with
  | bvar _ | iconst _ | bconst _ => rfl
  | fvar y =>
    simp only [Exp.fv, List.mem_singleton] at h
    simp only [Exp.subst, if_neg (fun hyx : y = x => h hyx.symm)]
  | lam e ih | not e ih | ann e _ ih =>
    simp only [Exp.fv] at h
    simp only [Exp.subst, ih h]
  | letin e₁ e₂ ih1 ih2 | app e₁ e₂ ih1 ih2 | and e₁ e₂ ih1 ih2
  | leq e₁ e₂ ih1 ih2 | add e₁ e₂ ih1 ih2 =>
    simp only [Exp.fv, List.mem_append, not_or] at h
    simp only [Exp.subst, ih1 h.1, ih2 h.2]
  | ite e₀ e₁ e₂ ih0 ih1 ih2 =>
    simp only [Exp.fv, List.mem_append, not_or] at h
    simp only [Exp.subst, ih0 h.1.1, ih1 h.1.2, ih2 h.2]

/-- Raw (unfiltered) free variables of a refinement; `Refinement.fv` is this with
    the reserved `ν` removed. (Replaces the old `r.fmla.fv` now that `Refinement`
    is an enum: for a κ-application it is the union of the argument terms' fvs.) -/
def Refinement.rawfv {b : Base} (r : Refinement b) : List EVar :=
  match r with
  | .fmla φ      => φ.fv
  | .kapp _ args => args.flatMap (fun a => Term.fv a.2)

theorem Refinement.fv_eq_rawfv_filter {b : Base} (r : Refinement b) :
    Refinement.fv r = (Refinement.rawfv r).filter (· ≠ nuName) := by
  cases r <;> rfl

/-- If `x ∉ r.fv` (= raw fv minus ν) and `x ≠ nuName`, then `x ∉ r.rawfv`. -/
theorem Refinement.fv_filter_of_ne_nu {b : Base} (r : Refinement b) (x : EVar)
    (hx : x ∉ r.fv) (hxν : x ≠ nuName) : x ∉ Refinement.rawfv r := by
  rw [Refinement.fv_eq_rawfv_filter, List.mem_filter] at hx
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

/-- Refinement-level: opening with `z` can only add `z` to the raw free vars. -/
private theorem Refinement.rawfv_openBVar_subset {b'' : Base} (b' : Base) (k : Nat) (z : EVar)
    (r : Refinement b'') :
    ∀ y ∈ Refinement.rawfv (r.openBVar b' k z), y = z ∨ y ∈ Refinement.rawfv r := by
  cases r with
  | fmla φ => exact Formula.fv_openBVar_subset b' k z φ
  | kapp kn args =>
    intro y hy
    simp only [Refinement.openBVar, Refinement.rawfv, List.mem_flatMap, List.mem_map] at hy ⊢
    obtain ⟨a, ⟨a₀, ha₀_mem, rfl⟩, hy_in⟩ := hy
    rcases Term.fv_openBVar_subset b' k z a₀.2 y hy_in with h | h
    · exact Or.inl h
    · exact Or.inr ⟨a₀, ha₀_mem, h⟩

/-- Opening `Ty` with `z` doesn't add any `x ≠ z` to the free variables. -/
theorem Ty.fv_openVar_not_mem (t : Ty) (k : Nat) (z x : EVar)
    (hx : x ∉ t.fv) (hxz : x ≠ z) : x ∉ (t.openVar k z).fv := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.openVar, Ty.fv, Refinement.fv_eq_rawfv_filter]
    intro hmem
    simp only [List.mem_filter] at hmem
    obtain ⟨hmem', hnu⟩ := hmem
    -- openVar opens both .int and .bool BVars; use rawfv_openBVar_subset twice
    rcases Refinement.rawfv_openBVar_subset .bool k z _ x hmem' with h | h
    · exact hxz h
    · rcases Refinement.rawfv_openBVar_subset .int k z r x h with h2 | h2
      · exact hxz h2
      · apply hx
        simp only [Ty.fv, Refinement.fv_eq_rawfv_filter, List.mem_filter]
        exact ⟨h2, hnu⟩
  | arrow s t ihs iht =>
    simp only [Ty.openVar, Ty.fv, List.mem_append, not_or]
    simp only [Ty.fv, List.mem_append, not_or] at hx
    exact ⟨ihs k hx.1, iht (k + 1) hx.2⟩

/-! ## 21. openBVar/openVar commutativity at different levels -/

/-- The 4-operation commutativity for Term: opening (int@i, bool@i) then (int@j, bool@j)
    equals opening (int@j, bool@j) then (int@i, bool@i), when i ≠ j.
    Each bvar is handled by exactly one of the four openers regardless of order. -/
private theorem Term.openBVar4_comm {b : Base} (t : Term b) (i j : Nat) (x y : EVar)
    (hij : i ≠ j) :
    (((t.openBVar .int i x).openBVar .bool i x).openBVar .int j y).openBVar .bool j y =
    (((t.openBVar .int j y).openBVar .bool j y).openBVar .int i x).openBVar .bool i x := by
  induction t with
  | const _ _ => simp [Term.openBVar]
  | fvar _ _  => simp [Term.openBVar]
  | bvar b' k =>
    cases b' <;>
    · simp only [Term.openBVar]
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [Term.openBVar, hij.symm]
  | add t1 t2 ih1 ih2 => simp only [Term.openBVar]; congr 1
  | not t ih           => simp [Term.openBVar, ih]
  | and t1 t2 ih1 ih2  => simp only [Term.openBVar]; congr 1

private theorem Formula.openBVar4_comm (φ : Formula) (i j : Nat) (x y : EVar) (hij : i ≠ j) :
    (((φ.openBVar .int i x).openBVar .bool i x).openBVar .int j y).openBVar .bool j y =
    (((φ.openBVar .int j y).openBVar .bool j y).openBVar .int i x).openBVar .bool i x := by
  induction φ with
  | tt | ff => simp [Formula.openBVar]
  | eqI t1 t2 | eqB t1 t2 | leqI t1 t2 =>
    simp only [Formula.openBVar]; congr 1
    · exact Term.openBVar4_comm t1 i j x y hij
    · exact Term.openBVar4_comm t2 i j x y hij
  | and φ1 φ2 ih1 ih2 | or φ1 φ2 ih1 ih2 | imp φ1 φ2 ih1 ih2 =>
    simp only [Formula.openBVar]; congr 1
  | not φ ih => simp [Formula.openBVar, ih]
  | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
    simp only [Formula.openBVar, ih]

private theorem Refinement.openBVar4_comm {b'' : Base} (r : Refinement b'') (i j : Nat)
    (x y : EVar) (hij : i ≠ j) :
    (((r.openBVar .int i x).openBVar .bool i x).openBVar .int j y).openBVar .bool j y =
    (((r.openBVar .int j y).openBVar .bool j y).openBVar .int i x).openBVar .bool i x := by
  cases r with
  | fmla φ => simp only [Refinement.openBVar]; rw [Formula.openBVar4_comm φ i j x y hij]
  | kapp kn args =>
    simp only [Refinement.openBVar, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact congrArg (Sigma.mk a.1) (Term.openBVar4_comm a.2 i j x y hij)

private theorem Term.openBVar_comm_same_base {b' : Base} (t : Term b') (b : Base) (i j : Nat)
    (x y : EVar) (hij : i ≠ j) :
    (t.openBVar b i x).openBVar b j y = (t.openBVar b j y).openBVar b i x := by
  induction t with
  | const _ _ => simp [Term.openBVar]
  | fvar _ _  => simp [Term.openBVar]
  | bvar b'' k' =>
    cases b'' <;> cases b <;>
      simp only [Term.openBVar] <;>
      by_cases hki : k' = i <;> by_cases hkj : k' = j <;>
        simp_all [Term.openBVar, hij.symm]
  | add t1 t2 ih1 ih2 => simp only [Term.openBVar]; congr 1
  | not t ih           => simp [Term.openBVar, ih]
  | and t1 t2 ih1 ih2  => simp only [Term.openBVar]; congr 1

/-- Opening a type at two different levels commutes. -/
theorem Ty.openVar_comm (t : Ty) (i j : Nat) (x y : EVar) (hij : i ≠ j) :
    (t.openVar i x).openVar j y = (t.openVar j y).openVar i x := by
  induction t generalizing i j with
  | refine b r =>
    simp only [Ty.openVar]
    exact congrArg (Ty.refine b) (Refinement.openBVar4_comm r i j x y hij)
  | arrow s t ihs iht =>
    simp only [Ty.openVar]
    congr 1
    · exact ihs i j hij
    · exact iht (i+1) (j+1) (by omega)

private theorem Formula.named_openBVar_not_mem (φ : Formula) (b : Base) (k : Nat) (z x : EVar)
    (hx : x ∉ φ.named) (_hxz : x ≠ z) : x ∉ (φ.openBVar b k z).named := by
  induction φ with
  | tt | ff | eqI _ _ | eqB _ _ | leqI _ _ => simp [Formula.openBVar, Formula.named]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.openBVar, Formula.named, List.mem_append, not_or] at *
    exact ⟨ih₁ hx.1, ih₂ hx.2⟩
  | not φ ih =>
    simp only [Formula.openBVar, Formula.named] at *
    exact ih hx
  | exI w φ ih | exB w φ ih | allI w φ ih | allB w φ ih =>
    simp only [Formula.openBVar, Formula.named, List.mem_cons, not_or] at *
    exact ⟨hx.1, ih hx.2⟩

private theorem Refinement.named_openBVar_not_mem {b'' : Base} (r : Refinement b'')
    (b : Base) (k : Nat) (z x : EVar) (hx : x ∉ r.named) (hxz : x ≠ z) :
    x ∉ (r.openBVar b k z).named := by
  cases r with
  | fmla φ => exact Formula.named_openBVar_not_mem φ b k z x hx hxz
  | kapp kn args => simp only [Refinement.openBVar, Refinement.named]; exact hx

theorem Ty.named_openVar_not_mem (t : Ty) (k : Nat) (z x : EVar)
    (hx : x ∉ Ty.named t) (hxz : x ≠ z) : x ∉ Ty.named (t.openVar k z) := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.openVar, Ty.named]
    simp only [Ty.named] at hx
    -- openVar opens both bases; apply named_openBVar_not_mem for .bool then .int
    exact Refinement.named_openBVar_not_mem _ .bool k z x
      (Refinement.named_openBVar_not_mem r .int k z x hx hxz) hxz
  | arrow s t ihs iht =>
    simp only [Ty.openVar, Ty.named, List.mem_append, not_or] at *
    exact ⟨ihs k hx.1, iht (k + 1) hx.2⟩

/-! ## 21. Formula.interp_substBV: substBV is the semantic analog of openBVar+update -/

private theorem Term.interp_substBV_eq {b'' : Base} (t : Term b'') (b : Base) (k : Nat)
    (v : b.interp) (x : EVar) (ρ : REnv)
    (hx : x ∉ t.fv) :
    Term.interp ρ (Term.substBV b k v t) = Term.interp (ρ.update b x v) (t.openBVar b k x) := by
  induction t with
  | const b' c => simp [Term.substBV, Term.openBVar, Term.interp]
  | bvar b' j =>
    cases b' <;> cases b
    · simp only [Term.substBV, Term.openBVar]
      by_cases hjk : j = k
      · simp [hjk, interp]
      · simp [hjk, Term.interp]
    · simp [Term.substBV, Term.openBVar, Term.interp]
    · simp [Term.substBV, Term.openBVar, Term.interp]
    · simp only [Term.substBV, Term.openBVar]
      by_cases hjk : j = k
      · simp [hjk, interp]
      · simp [hjk, Term.interp]
  | fvar b' z =>
    have hxz : x ≠ z := fun h => hx (by subst h; simp [Term.fv])
    simp only [Term.substBV, Term.openBVar, Term.interp]
    cases b' <;> cases b <;>
      simp_all [REnv.get]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append] at hx
    simp [Term.substBV, Term.openBVar, Term.interp,
          ih₁ (fun h => hx (Or.inl h)), ih₂ (fun h => hx (Or.inr h))]
  | not t ih =>
    simp only [Term.fv] at hx
    simp [Term.substBV, Term.openBVar, Term.interp, ih hx]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append] at hx
    simp [Term.substBV, Term.openBVar, Term.interp,
          ih₁ (fun h => hx (Or.inl h)), ih₂ (fun h => hx (Or.inr h))]

private theorem REnv.update_comm_gen (ρ : REnv) (b : Base) (x : EVar) (v : b.interp)
    (b' : Base) (y : EVar) (w : b'.interp) (hxy : x ≠ y) :
    (ρ.update b x v).update b' y w = (ρ.update b' y w).update b x v := by
  apply REnv.ext; funext z
  cases b <;> cases b' <;>
    by_cases hxz : x = z <;> by_cases hyz : y = z <;>
    simp_all

theorem Formula.interp_substBV (φ : Formula) (b : Base) (k : Nat)
    (v : b.interp) (x : EVar) (ρ : REnv)
    (hx : x ∉ φ.fv) (hxn : x ∉ φ.named) :
    Formula.interp ρ (φ.substBV b k v) ↔
    Formula.interp (ρ.update b x v) (φ.openBVar b k x) := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  revert hx hxn ρ
  induction φ with
  | tt => intros; simp [Formula.substBV, Formula.openBVar, Formula.interp]
  | ff => intros; simp [Formula.substBV, Formula.openBVar, Formula.interp]
  | eqI t₁ t₂ =>
    intro ρ hx _
    simp only [Formula.fv] at hx
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    rw [Term.interp_substBV_eq t₁ b k v x ρ (not_mem_l _ _ _ hx),
        Term.interp_substBV_eq t₂ b k v x ρ (not_mem_r _ _ _ hx)]
  | eqB t₁ t₂ =>
    intro ρ hx _
    simp only [Formula.fv] at hx
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    rw [Term.interp_substBV_eq t₁ b k v x ρ (not_mem_l _ _ _ hx),
        Term.interp_substBV_eq t₂ b k v x ρ (not_mem_r _ _ _ hx)]
  | leqI t₁ t₂ =>
    intro ρ hx _
    simp only [Formula.fv] at hx
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    rw [Term.interp_substBV_eq t₁ b k v x ρ (not_mem_l _ _ _ hx),
        Term.interp_substBV_eq t₂ b k v x ρ (not_mem_r _ _ _ hx)]
  | and φ₁ φ₂ ih₁ ih₂ =>
    intro ρ hx hxn
    simp only [Formula.fv, Formula.named, List.mem_append, not_or] at hx hxn
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    exact and_congr (ih₁ ρ hx.1 hxn.1) (ih₂ ρ hx.2 hxn.2)
  | or φ₁ φ₂ ih₁ ih₂ =>
    intro ρ hx hxn
    simp only [Formula.fv, Formula.named, List.mem_append, not_or] at hx hxn
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    exact or_congr (ih₁ ρ hx.1 hxn.1) (ih₂ ρ hx.2 hxn.2)
  | not φ ih =>
    intro ρ hx hxn
    simp only [Formula.fv, Formula.named] at hx hxn
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    exact not_congr (ih ρ hx hxn)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro ρ hx hxn
    simp only [Formula.fv, Formula.named, List.mem_append, not_or] at hx hxn
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    exact imp_congr (ih₁ ρ hx.1 hxn.1) (ih₂ ρ hx.2 hxn.2)
  | exI y φ ih =>
    intro ρ hx hxn
    simp only [Formula.fv, List.mem_filter, not_and] at hx
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hxφfv : x ∉ φ.fv := by grind
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h := (ih (ρ.update .int y n) hxφfv hxn.2).mp hn
      rwa [← REnv.update_comm_gen ρ b x v .int y n hxn.1] at h
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply (ih (ρ.update .int y n) hxφfv hxn.2).mpr
      rw [← REnv.update_comm_gen ρ b x v .int y n hxn.1]
      exact hn
  | exB y φ ih =>
    intro ρ hx hxn
    simp only [Formula.fv, List.mem_filter, not_and] at hx
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hxφfv : x ∉ φ.fv := by grind
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    constructor
    · rintro ⟨bv, hbv⟩
      refine ⟨bv, ?_⟩
      have h := (ih (ρ.update .bool y bv) hxφfv hxn.2).mp hbv
      rwa [← REnv.update_comm_gen ρ b x v .bool y bv hxn.1] at h
    · rintro ⟨bv, hbv⟩
      refine ⟨bv, ?_⟩
      apply (ih (ρ.update .bool y bv) hxφfv hxn.2).mpr
      rw [← REnv.update_comm_gen ρ b x v .bool y bv hxn.1]
      exact hbv
  | allI y φ ih =>
    intro ρ hx hxn
    simp only [Formula.fv, List.mem_filter, not_and] at hx
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hxφfv : x ∉ φ.fv := by grind
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    constructor
    · intro hf n
      have h := (ih (ρ.update .int y n) hxφfv hxn.2).mp (hf n)
      rwa [← REnv.update_comm_gen ρ b x v .int y n hxn.1] at h
    · intro hf n
      apply (ih (ρ.update .int y n) hxφfv hxn.2).mpr
      rw [← REnv.update_comm_gen ρ b x v .int y n hxn.1]
      exact hf n
  | allB y φ ih =>
    intro ρ hx hxn
    simp only [Formula.fv, List.mem_filter, not_and] at hx
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hxφfv : x ∉ φ.fv := by grind
    simp only [Formula.substBV, Formula.openBVar, Formula.interp]
    constructor
    · intro hf bv
      have h := (ih (ρ.update .bool y bv) hxφfv hxn.2).mp (hf bv)
      rwa [← REnv.update_comm_gen ρ b x v .bool y bv hxn.1] at h
    · intro hf bv
      apply (ih (ρ.update .bool y bv) hxφfv hxn.2).mpr
      rw [← REnv.update_comm_gen ρ b x v .bool y bv hxn.1]
      exact hf bv

/-- Refinement-level `interp_substBV`: substituting a bound value equals opening
    with a fresh `x` then updating `x` to that value (the semantic counterpart of
    `Refinement.openBVar`). Both constructors reduce to the `Term`/`Formula`
    versions plus a `nuName`/`x` update commutation. -/
theorem Refinement.interp_substBV (κ : KEnv) {b' : Base} (r : Refinement b') (b : Base)
    (k : Nat) (v : b.interp) (x : EVar) (ρ : REnv) {w : b'.interp}
    (hx : x ∉ Refinement.rawfv r) (hxn : x ∉ Refinement.named r) (hxν : x ≠ nuName) :
    Refinement.interp κ (r.substBV b k v) ρ w ↔
    Refinement.interp κ (r.openBVar b k x) (ρ.update b x v) w := by
  cases r with
  | fmla φ =>
    simp only [Refinement.rawfv, Refinement.named] at hx hxn
    simp only [Refinement.interp, Refinement.substBV, Refinement.openBVar]
    rw [Formula.interp_substBV φ b k v x (ρ.update b' nuName w) hx hxn,
        REnv.update_comm_gen ρ b' nuName w b x v hxν.symm]
  | kapp kn args =>
    simp only [Refinement.interp, Refinement.substBV, Refinement.openBVar]
    apply Iff.of_eq
    congr 1
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro a ha
    have hxa : x ∉ Term.fv a.2 := fun hm =>
      hx (by simp only [Refinement.rawfv, List.mem_flatMap]; exact ⟨a, ha, hm⟩)
    simp only [Function.comp]
    congr 1
    rw [Term.interp_substBV_eq a.2 b k v x (ρ.update b' nuName w) hxa,
        REnv.update_comm_gen ρ b' nuName w b x v hxν.symm]

/-! ## 22. substBV preserves fv/named subsets -/

private theorem Term.fv_substBV_not_mem {b'' : Base} (t : Term b'') (b : Base) (k : Nat)
    (v : b.interp) (x : EVar) (hx : x ∉ t.fv) :
    x ∉ (Term.substBV b k v t).fv := by
  induction t with
  | const _ _ => simp [Term.substBV, Term.fv]
  | bvar b' j =>
    simp only [Term.substBV]
    cases b <;> cases b' <;> simp_all [Term.fv]
    all_goals (by_cases j = k <;> simp_all [Term.fv])
  | fvar _ y => simp [Term.substBV, Term.fv] at *; exact hx
  | add t₁ t₂ ih1 ih2 =>
    simp only [Term.substBV, Term.fv, List.mem_append, not_or] at *
    exact ⟨ih1 hx.1, ih2 hx.2⟩
  | not t ih =>
    simp only [Term.substBV, Term.fv] at *
    exact ih hx
  | and t₁ t₂ ih1 ih2 =>
    simp only [Term.substBV, Term.fv, List.mem_append, not_or] at *
    exact ⟨ih1 hx.1, ih2 hx.2⟩

private theorem Formula.substBV_fv_not_mem (φ : Formula) (b : Base) (k : Nat)
    (v : b.interp) (x : EVar) (hx : x ∉ φ.fv) :
    x ∉ (φ.substBV b k v).fv := by
  induction φ with
  | tt | ff => simp [Formula.substBV, Formula.fv]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.substBV, Formula.fv, List.mem_append, not_or] at *
    exact ⟨Term.fv_substBV_not_mem _ b k v x hx.1,
           Term.fv_substBV_not_mem _ b k v x hx.2⟩
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp only [Formula.substBV, Formula.fv, List.mem_append, not_or] at *
    exact ⟨ih1 hx.1, ih2 hx.2⟩
  | not φ ih =>
    simp only [Formula.substBV, Formula.fv] at *
    exact ih hx
  | exI y φ ih | exB y φ ih | allI y φ ih | allB y φ ih =>
    simp only [Formula.substBV, Formula.fv, List.mem_filter] at *
    intro ⟨hmem, hxy⟩
    grind

/-- Refinement-level: `substBV` does not introduce a new (raw) free variable. -/
private theorem Refinement.substBV_rawfv_not_mem {b'' : Base} (r : Refinement b'')
    (b : Base) (k : Nat) (v : b.interp) (x : EVar) (hx : x ∉ Refinement.rawfv r) :
    x ∉ Refinement.rawfv (r.substBV b k v) := by
  cases r with
  | fmla φ => exact Formula.substBV_fv_not_mem φ b k v x hx
  | kapp kn args =>
    simp only [Refinement.substBV, Refinement.rawfv, List.mem_flatMap] at *
    intro ⟨a, ha, hmem⟩
    simp only [List.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    grind [Term.fv_substBV_not_mem]

/-- `Refinement.fv` (raw fv minus ν) is not grown by `substBV`. -/
private theorem Refinement.fv_substBV_not_mem {b'' : Base} (r : Refinement b'')
    (b : Base) (k : Nat) (v : b.interp) (x : EVar) (hx : x ∉ Refinement.fv r) :
    x ∉ Refinement.fv (r.substBV b k v) := by
  cases r with
  | fmla φ =>
    simp only [Refinement.substBV, Refinement.fv, List.mem_filter] at hx ⊢
    grind [Formula.substBV_fv_not_mem]
  | kapp kn args =>
    simp only [Refinement.substBV, Refinement.fv, List.mem_filter,
               List.mem_flatMap, List.mem_map] at hx ⊢
    grind [Term.fv_substBV_not_mem]

private theorem Formula.substBV_named_not_mem (φ : Formula) (b : Base) (k : Nat)
    (v : b.interp) (x : EVar) (hx : x ∉ φ.named) :
    x ∉ (φ.substBV b k v).named := by
  induction φ with
  | tt | ff | eqI _ _ | eqB _ _ | leqI _ _ => simp [Formula.substBV, Formula.named]
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp only [Formula.substBV, Formula.named, List.mem_append, not_or] at *
    exact ⟨ih1 hx.1, ih2 hx.2⟩
  | not φ ih =>
    simp only [Formula.substBV, Formula.named] at *
    exact ih hx
  | exI y φ ih | exB y φ ih | allI y φ ih | allB y φ ih =>
    simp only [Formula.substBV, Formula.named, List.mem_cons, not_or] at *
    exact ⟨hx.1, ih hx.2⟩

/-- Refinement-level: `substBV` does not introduce a new named binder. -/
private theorem Refinement.substBV_named_not_mem {b'' : Base} (r : Refinement b'')
    (b : Base) (k : Nat) (v : b.interp) (x : EVar) (hx : x ∉ r.named) :
    x ∉ (r.substBV b k v).named := by
  cases r with
  | fmla φ => exact Formula.substBV_named_not_mem φ b k v x hx
  | kapp kn args => simp only [Refinement.substBV, Refinement.named]; exact hx

theorem Ty.fv_substBV_not_mem (t : Ty) (x : EVar) (va : Val) (hx : x ∉ t.fv) :
    x ∉ (t.substBV va).fv := by
  simp only [Ty.substBV]
  suffices h : ∀ k, x ∉ (t.substBV_aux k va).fv from h 0
  induction t with
  | refine b r =>
    intro k
    cases va <;> simp only [Ty.substBV_aux, Ty.fv]
    · -- .iconst n
      exact Refinement.fv_substBV_not_mem r .int k _ x hx
    · -- .bconst bv
      exact Refinement.fv_substBV_not_mem r .bool k _ x hx
    · -- .clos: unchanged
      exact hx
  | arrow s t ihs iht =>
    intro k
    simp only [Ty.fv, List.mem_append, not_or] at hx
    simp only [Ty.substBV_aux, Ty.fv, List.mem_append, not_or]
    exact ⟨ihs hx.1 k, iht hx.2 (k + 1)⟩

theorem Ty.named_substBV_not_mem (t : Ty) (x : EVar) (va : Val) (hx : x ∉ Ty.named t) :
    x ∉ Ty.named (t.substBV va) := by
  simp only [Ty.substBV]
  suffices h : ∀ k, x ∉ Ty.named (t.substBV_aux k va) from h 0
  induction t with
  | refine b r =>
    intro k
    simp only [Ty.named] at hx
    cases va <;> simp only [Ty.substBV_aux, Ty.named]
    · exact Refinement.substBV_named_not_mem r .int k _ x hx
    · exact Refinement.substBV_named_not_mem r .bool k _ x hx
    · exact hx
  | arrow s t ihs iht =>
    intro k
    simp only [Ty.named, List.mem_append, not_or] at hx
    simp only [Ty.substBV_aux, Ty.named, List.mem_append, not_or]
    exact ⟨ihs hx.1 k, iht hx.2 (k + 1)⟩

/-! ## Rename keystone: openBVar then replaceFVar -/

/-- Opening a term at `y` factors as opening at `x` and then renaming `x → y`,
    provided `x` does not already occur free. -/
theorem Term.openBVar_replace {b' b : Base} (k : Nat) (x y : EVar)
    (t : Term b) (hx : x ∉ Term.fv t) :
    (t.openBVar b' k x).replaceFVar x y = t.openBVar b' k y := by
  induction t with
  | const _ _    => simp [Term.openBVar, Term.replaceFVar]
  | bvar b'' j   =>
    cases b'' <;> cases b' <;>
      simp only [Term.openBVar] <;>
      (try (split <;> simp_all [Term.replaceFVar]))
  | fvar b'' z   =>
    simp only [Term.fv, List.mem_singleton] at hx
    have hzne : z ≠ x := fun h => hx h.symm
    simp [Term.openBVar, Term.replaceFVar, hzne]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at hx
    simp [Term.openBVar, Term.replaceFVar, ih₁ hx.1, ih₂ hx.2]
  | not t ih =>
    simp only [Term.fv] at hx
    simp [Term.openBVar, Term.replaceFVar, ih hx]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at hx
    simp [Term.openBVar, Term.replaceFVar, ih₁ hx.1, ih₂ hx.2]

/-- Opening a formula at `y` factors as opening at `x` followed by `x → y`
    rename, provided `x` does not appear free and `x` is not a bound name. -/
theorem Formula.openBVar_replace (b' : Base) (k : Nat) (x y : EVar) (φ : Formula)
    (hx : x ∉ Formula.fv φ) (hxn : x ∉ Formula.named φ) :
    (φ.openBVar b' k x).replaceFVar x y = φ.openBVar b' k y := by
  induction φ generalizing k with
  | tt | ff => simp [Formula.openBVar, Formula.replaceFVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hx
    simp [Formula.openBVar, Formula.replaceFVar,
          Term.openBVar_replace k x y _ hx.1, Term.openBVar_replace k x y _ hx.2]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named, List.mem_append, not_or] at hx hxn
    simp [Formula.openBVar, Formula.replaceFVar,
          ih₁ k hx.1 hxn.1, ih₂ k hx.2 hxn.2]
  | not φ ih =>
    simp only [Formula.fv, Formula.named] at hx hxn
    simp [Formula.openBVar, Formula.replaceFVar, ih k hx hxn]
  | exI z φ ih | exB z φ ih | allI z φ ih | allB z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hzne : z ≠ x := fun h => hxn.1 h.symm
    have hxfv : x ∉ φ.fv := by
      intro hmem
      apply hx
      simp [Formula.fv, List.mem_filter]
      exact ⟨hmem, Ne.symm hzne⟩
    simp only [Formula.openBVar, Formula.replaceFVar, if_neg hzne, ih k hxfv hxn.2]

/-- Refinement counterpart of `Formula.openBVar_replace`. -/
theorem Refinement.openBVar_replace {b'' : Base} (b' : Base) (k : Nat) (x y : EVar)
    (r : Refinement b'')
    (hx : x ∉ Refinement.rawfv r) (hxn : x ∉ Refinement.named r) :
    (r.openBVar b' k x).replaceFVar x y = r.openBVar b' k y := by
  cases r with
  | fmla φ =>
    simp only [Refinement.openBVar, Refinement.replaceFVar]
    rw [Formula.openBVar_replace b' k x y φ hx hxn]
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.replaceFVar]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro ⟨b''', t⟩ hmem
    show Sigma.mk b''' ((t.openBVar b' k x).replaceFVar x y) =
         Sigma.mk b''' (t.openBVar b' k y)
    have hxt : x ∉ Term.fv t := by
      intro hmemT
      apply hx
      simp only [Refinement.rawfv, List.mem_flatMap]
      exact ⟨⟨b''', t⟩, hmem, hmemT⟩
    rw [Term.openBVar_replace k x y t hxt]

/-! ## Commuting openBVar past replaceFVar (no freshness on `x` required) -/

/-- Renaming a term commutes with opening: opening at `x` then renaming `x → y`
    equals renaming `x → y` then opening at `y`. -/
theorem Term.openBVar_replaceFVar_chain {b' b : Base} (k : Nat) (x y : EVar)
    (t : Term b) :
    (t.openBVar b' k x).replaceFVar x y =
    (t.replaceFVar x y).openBVar b' k y := by
  induction t with
  | const _ _    => simp [Term.openBVar, Term.replaceFVar]
  | bvar b'' j   =>
    cases b'' <;> cases b' <;>
      simp only [Term.openBVar, Term.replaceFVar] <;>
      (try (split <;> simp_all [Term.replaceFVar]))
  | fvar b'' z   =>
    by_cases hzx : z = x <;>
      cases b'' <;>
      simp_all [Term.openBVar, Term.replaceFVar]
  | add t₁ t₂ ih₁ ih₂ => simp [Term.openBVar, Term.replaceFVar, ih₁, ih₂]
  | not t ih          => simp [Term.openBVar, Term.replaceFVar, ih]
  | and t₁ t₂ ih₁ ih₂ => simp [Term.openBVar, Term.replaceFVar, ih₁, ih₂]

/-- Renaming a formula commutes with opening, provided the rename source is
    not also a bound name in any inner binder. -/
theorem Formula.openBVar_replaceFVar_chain (b' : Base) (k : Nat) (x y : EVar)
    (φ : Formula) (hxn : x ∉ Formula.named φ) :
    (φ.openBVar b' k x).replaceFVar x y =
    (φ.replaceFVar x y).openBVar b' k y := by
  induction φ generalizing k with
  | tt | ff => simp [Formula.openBVar, Formula.replaceFVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp [Formula.openBVar, Formula.replaceFVar,
          Term.openBVar_replaceFVar_chain k x y t₁,
          Term.openBVar_replaceFVar_chain k x y t₂]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.named, List.mem_append, not_or] at hxn
    simp [Formula.openBVar, Formula.replaceFVar, ih₁ k hxn.1, ih₂ k hxn.2]
  | not φ ih =>
    simp only [Formula.named] at hxn
    simp [Formula.openBVar, Formula.replaceFVar, ih k hxn]
  | exI z φ ih | exB z φ ih | allI z φ ih | allB z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hzx : z ≠ x := fun h => hxn.1 h.symm
    simp only [Formula.openBVar, Formula.replaceFVar, if_neg hzx, ih k hxn.2]

/-- Refinement-level chain version. -/
theorem Refinement.openBVar_replaceFVar_chain {b'' : Base} (b' : Base) (k : Nat)
    (x y : EVar) (r : Refinement b'') (hxn : x ∉ Refinement.named r) :
    (r.openBVar b' k x).replaceFVar x y =
    (r.replaceFVar x y).openBVar b' k y := by
  cases r with
  | fmla φ =>
    simp only [Refinement.openBVar, Refinement.replaceFVar]
    rw [Formula.openBVar_replaceFVar_chain b' k x y φ hxn]
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.replaceFVar]
    congr 1
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro ⟨b''', t⟩ _
    show Sigma.mk b''' ((t.openBVar b' k x).replaceFVar x y) =
         Sigma.mk b''' ((t.replaceFVar x y).openBVar b' k y)
    rw [Term.openBVar_replaceFVar_chain k x y t]

/-! ## replaceFVar is identity on fresh terms/formulas/refinements -/

theorem Term.replaceFVar_id_of_fresh {b : Base} (t : Term b) (x y : EVar)
    (hx : x ∉ Term.fv t) : t.replaceFVar x y = t := by
  induction t with
  | const _ _ => rfl
  | bvar _ _  => rfl
  | fvar b' z =>
    simp only [Term.fv, List.mem_singleton] at hx
    have : z ≠ x := fun h => hx h.symm
    simp [Term.replaceFVar, this]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at hx
    simp [Term.replaceFVar, ih₁ hx.1, ih₂ hx.2]
  | not t ih =>
    simp only [Term.fv] at hx
    simp [Term.replaceFVar, ih hx]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at hx
    simp [Term.replaceFVar, ih₁ hx.1, ih₂ hx.2]

theorem Formula.replaceFVar_id_of_fresh (φ : Formula) (x y : EVar)
    (hx : x ∉ Formula.fv φ) : φ.replaceFVar x y = φ := by
  induction φ with
  | tt | ff => rfl
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hx
    simp [Formula.replaceFVar,
          Term.replaceFVar_id_of_fresh t₁ x y hx.1,
          Term.replaceFVar_id_of_fresh t₂ x y hx.2]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hx
    simp [Formula.replaceFVar, ih₁ hx.1, ih₂ hx.2]
  | not φ ih =>
    simp only [Formula.fv] at hx
    simp [Formula.replaceFVar, ih hx]
  | exI z φ ih | exB z φ ih | allI z φ ih | allB z φ ih =>
    simp only [Formula.replaceFVar]
    by_cases hzx : z = x
    · simp [hzx]
    · simp only [if_neg hzx]
      congr 1
      apply ih
      intro hmem
      apply hx
      simp [Formula.fv, List.mem_filter]
      exact ⟨hmem, fun h => hzx h.symm⟩

theorem Refinement.replaceFVar_id_of_fresh {b'' : Base} (r : Refinement b'')
    (x y : EVar) (hx : x ∉ Refinement.rawfv r) :
    r.replaceFVar x y = r := by
  cases r with
  | fmla φ =>
    simp only [Refinement.replaceFVar]
    rw [Formula.replaceFVar_id_of_fresh φ x y hx]
  | kapp kn args =>
    simp only [Refinement.replaceFVar]
    congr 1
    have hall : ∀ a ∈ args, x ∉ Term.fv a.snd := by
      intro a hmem hmemT
      apply hx
      simp only [Refinement.rawfv, List.mem_flatMap]
      exact ⟨a, hmem, hmemT⟩
    clear hx
    induction args with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.cons.injEq]
      obtain ⟨b''', t⟩ := hd
      refine ⟨?_, ih (fun a hmem => hall a (List.mem_cons_of_mem _ hmem))⟩
      show Sigma.mk b''' (t.replaceFVar x y) = Sigma.mk b''' t
      rw [Term.replaceFVar_id_of_fresh t x y (hall ⟨b''', t⟩ List.mem_cons_self)]

/-! ## Ty.replaceFVar and Ty.openVar_replace -/

/-- Rename free occurrences of `x` to `y` throughout a type's refinements. -/
def Ty.replaceFVar (x y : EVar) : Ty → Ty
  | .refine b r => .refine b (r.replaceFVar x y)
  | .arrow s t  => .arrow (s.replaceFVar x y) (t.replaceFVar x y)

/-- Combined int+bool opening chain. Used by `Ty.openVar_replace` for the
    `.refine` case where `Ty.openVar` opens at both bases at once. The
    precondition refers to the *original* `φ`'s named set, avoiding the issue
    that opening at one base may grow `Formula.named` of the intermediate. -/
theorem Formula.openBVar2_replaceFVar_chain (k : Nat) (x y : EVar) (φ : Formula)
    (hxn : x ∉ Formula.named φ) :
    ((φ.openBVar .int k x).openBVar .bool k x).replaceFVar x y =
    ((φ.replaceFVar x y).openBVar .int k y).openBVar .bool k y := by
  induction φ generalizing k with
  | tt | ff => simp [Formula.openBVar, Formula.replaceFVar]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.openBVar, Formula.replaceFVar,
               Term.openBVar_replaceFVar_chain k x y (t₁.openBVar .int k x),
               Term.openBVar_replaceFVar_chain k x y (t₂.openBVar .int k x),
               Term.openBVar_replaceFVar_chain k x y t₁,
               Term.openBVar_replaceFVar_chain k x y t₂]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.named, List.mem_append, not_or] at hxn
    simp [Formula.openBVar, Formula.replaceFVar, ih₁ k hxn.1, ih₂ k hxn.2]
  | not φ ih =>
    simp only [Formula.named] at hxn
    simp [Formula.openBVar, Formula.replaceFVar, ih k hxn]
  | exI z φ ih | exB z φ ih | allI z φ ih | allB z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn
    have hzx : z ≠ x := fun h => hxn.1 h.symm
    simp only [Formula.openBVar, Formula.replaceFVar, if_neg hzx, ih k hxn.2]

/-- Refinement-level combined int+bool chain. -/
theorem Refinement.openBVar2_replaceFVar_chain {b'' : Base} (k : Nat) (x y : EVar)
    (r : Refinement b'') (hxn : x ∉ Refinement.named r) :
    ((r.openBVar .int k x).openBVar .bool k x).replaceFVar x y =
    ((r.replaceFVar x y).openBVar .int k y).openBVar .bool k y := by
  cases r with
  | fmla φ =>
    simp only [Refinement.openBVar, Refinement.replaceFVar]
    rw [Formula.openBVar2_replaceFVar_chain k x y φ hxn]
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.replaceFVar]
    congr 1
    rw [List.map_map, List.map_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro ⟨b''', t⟩ _
    show Sigma.mk b''' (((t.openBVar .int k x).openBVar .bool k x).replaceFVar x y) =
         Sigma.mk b''' (((t.replaceFVar x y).openBVar .int k y).openBVar .bool k y)
    rw [Term.openBVar_replaceFVar_chain k x y (t.openBVar .int k x),
        Term.openBVar_replaceFVar_chain k x y t]

/-- `Ty.replaceFVar` is the identity on types where `x` is not free (and is
    distinct from `nuName`, since `Ty.fv` filters out the reserved `ν`). -/
theorem Ty.replaceFVar_id_of_fresh (t : Ty) (x y : EVar)
    (hx : x ∉ t.fv) (hxν : x ≠ nuName) :
    t.replaceFVar x y = t := by
  induction t with
  | refine b r =>
    have hxfv : x ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r x hx hxν
    simp [Ty.replaceFVar, Refinement.replaceFVar_id_of_fresh r x y hxfv]
  | arrow s t ihs iht =>
    simp only [Ty.fv, List.mem_append, not_or] at hx
    simp [Ty.replaceFVar, ihs hx.1, iht hx.2]

/-- Opening at `y` factors as opening at `x` followed by a rename, provided
    `x` is fresh (free in neither the type nor among its named binders) and
    distinct from `nuName`. -/
theorem Ty.openVar_replace (k : Nat) (x y : EVar) (t : Ty)
    (hx : x ∉ t.fv) (hxn : x ∉ Ty.named t) (hxν : x ≠ nuName) :
    (t.openVar k x).replaceFVar x y = t.openVar k y := by
  induction t generalizing k with
  | refine b r =>
    simp only [Ty.named] at hxn
    have hxfv : x ∉ Refinement.rawfv r := Refinement.fv_filter_of_ne_nu r x hx hxν
    simp only [Ty.openVar, Ty.replaceFVar]
    rw [Refinement.openBVar2_replaceFVar_chain k x y r hxn,
        show r.replaceFVar x y = r from Refinement.replaceFVar_id_of_fresh r x y hxfv]
  | arrow s t ihs iht =>
    simp only [Ty.fv, List.mem_append, not_or] at hx
    simp only [Ty.named, List.mem_append, not_or] at hxn
    simp [Ty.openVar, Ty.replaceFVar,
          ihs k hx.1 hxn.1, iht (k + 1) hx.2 hxn.2]

/-! ## Rename keystone: interpretation

  Under the single-map `REnv`, renaming `x → y` corresponds to copying `y`'s
  (single) cell into `x` with the Val-level `write`. (The old two-field version
  set `x`'s int- and bool-slots independently to `y`'s; that has no single-map
  analogue, since one cell cannot hold both an `Int` and a `Bool` at once.) -/

theorem REnv.get_write_self (b : Base) (ρ : REnv) (x : EVar) (v : Val) :
    REnv.get b (ρ.write x v) x = v.proj b := by
  simp [REnv.get, REnv.lookup]

theorem REnv.get_write_other (b : Base) (ρ : REnv) (x : EVar) (v : Val) {y : EVar}
    (h : x ≠ y) : REnv.get b (ρ.write x v) y = REnv.get b ρ y := by
  have hxy : (x == y) = false := by simp [h]
  simp [REnv.get, REnv.lookup, hxy]

/-- `write` at `x` commutes with `update` at a different key `z`. -/
theorem REnv.write_update_comm (b : Base) (ρ : REnv) (z : EVar) (n : b.interp)
    (x : EVar) (v : Val) (h : x ≠ z) :
    (ρ.update b z n).write x v = (ρ.write x v).update b z n := by
  apply REnv.ext; funext w
  by_cases hxw : x = w <;> by_cases hzw : z = w <;>
    simp_all

theorem REnv.lookup_update_other (b : Base) (ρ : REnv) (z : EVar) (n : b.interp)
    {y : EVar} (h : z ≠ y) : (ρ.update b z n).lookup y = ρ.lookup y :=
  REnv.map_update_other b ρ z n h

/-- Interpretation of a term after renaming `x → y` equals interpretation under
    the environment with `y`'s cell copied into `x`. -/
theorem Term.interp_replaceFVar {b : Base} (t : Term b) (x y : EVar) (ρ : REnv) :
    Term.interp ρ (t.replaceFVar x y) =
    Term.interp (ρ.write x (ρ.lookup y)) t := by
  induction t with
  | const _ _  => simp [Term.replaceFVar, Term.interp]
  | bvar b' _  => cases b' <;> simp [Term.replaceFVar, Term.interp]
  | fvar b' z  =>
    by_cases hzx : z = x
    · subst hzx
      simp [Term.replaceFVar, Term.interp, REnv.get, REnv.lookup]
    · simp only [Term.replaceFVar, Term.interp, if_neg hzx]
      exact (REnv.get_write_other b' ρ x (ρ.lookup y) (Ne.symm hzx)).symm
  | add t₁ t₂ ih₁ ih₂ => simp [Term.replaceFVar, Term.interp, ih₁, ih₂]
  | not t ih          => simp [Term.replaceFVar, Term.interp, ih]
  | and t₁ t₂ ih₁ ih₂ => simp [Term.replaceFVar, Term.interp, ih₁, ih₂]

theorem Formula.interp_replaceFVar (φ : Formula) (x y : EVar) (ρ : REnv)
    (hxn : x ∉ φ.named) (hyn : y ∉ φ.named) :
    Formula.interp ρ (φ.replaceFVar x y) ↔
    Formula.interp (ρ.write x (ρ.lookup y)) φ := by
  induction φ generalizing ρ with
  | tt | ff => simp [Formula.replaceFVar, Formula.interp]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.replaceFVar, Formula.interp,
               Term.interp_replaceFVar t₁ x y ρ, Term.interp_replaceFVar t₂ x y ρ]
  | and φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.named, List.mem_append, not_or] at hxn hyn
    simp [Formula.replaceFVar, Formula.interp,
          ih₁ ρ hxn.1 hyn.1, ih₂ ρ hxn.2 hyn.2]
  | or φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.named, List.mem_append, not_or] at hxn hyn
    simp [Formula.replaceFVar, Formula.interp,
          ih₁ ρ hxn.1 hyn.1, ih₂ ρ hxn.2 hyn.2]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.named, List.mem_append, not_or] at hxn hyn
    simp [Formula.replaceFVar, Formula.interp,
          ih₁ ρ hxn.1 hyn.1, ih₂ ρ hxn.2 hyn.2]
  | not φ ih =>
    simp only [Formula.named] at hxn hyn
    simp [Formula.replaceFVar, Formula.interp, ih ρ hxn hyn]
  | exI z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn hyn
    have hzx : z ≠ x := fun h => hxn.1 h.symm
    have hzy : z ≠ y := fun h => hyn.1 h.symm
    simp only [Formula.replaceFVar, if_neg hzx, Formula.interp]
    refine exists_congr (fun n => ?_)
    rw [ih (ρ.update .int z n) hxn.2 hyn.2,
        REnv.lookup_update_other .int ρ z n hzy,
        REnv.write_update_comm .int ρ z n x (ρ.lookup y) (Ne.symm hzx)]
  | exB z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn hyn
    have hzx : z ≠ x := fun h => hxn.1 h.symm
    have hzy : z ≠ y := fun h => hyn.1 h.symm
    simp only [Formula.replaceFVar, if_neg hzx, Formula.interp]
    refine exists_congr (fun bv => ?_)
    rw [ih (ρ.update .bool z bv) hxn.2 hyn.2,
        REnv.lookup_update_other .bool ρ z bv hzy,
        REnv.write_update_comm .bool ρ z bv x (ρ.lookup y) (Ne.symm hzx)]
  | allI z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn hyn
    have hzx : z ≠ x := fun h => hxn.1 h.symm
    have hzy : z ≠ y := fun h => hyn.1 h.symm
    simp only [Formula.replaceFVar, if_neg hzx, Formula.interp]
    refine forall_congr' (fun n => ?_)
    rw [ih (ρ.update .int z n) hxn.2 hyn.2,
        REnv.lookup_update_other .int ρ z n hzy,
        REnv.write_update_comm .int ρ z n x (ρ.lookup y) (Ne.symm hzx)]
  | allB z φ ih =>
    simp only [Formula.named, List.mem_cons, not_or] at hxn hyn
    have hzx : z ≠ x := fun h => hxn.1 h.symm
    have hzy : z ≠ y := fun h => hyn.1 h.symm
    simp only [Formula.replaceFVar, if_neg hzx, Formula.interp]
    refine forall_congr' (fun bv => ?_)
    rw [ih (ρ.update .bool z bv) hxn.2 hyn.2,
        REnv.lookup_update_other .bool ρ z bv hzy,
        REnv.write_update_comm .bool ρ z bv x (ρ.lookup y) (Ne.symm hzx)]

/-! ## write-at-fresh-variable invariance of interpretation

  Writing *any* `Val` at a name not occurring in a term/formula leaves its
  interpretation unchanged. Generalizes `interp_update_fresh_*` to arbitrary
  written values (incl. closures) — needed because the merged extension
  `ρ.write`.write may store a closure at a fresh higher-order binder. -/

theorem Term.interp_write_fresh {b : Base} (t : Term b)
    (x : EVar) (v : Val) (ρ : REnv) (h : x ∉ t.fv) :
    Term.interp (ρ.write x v) t = Term.interp ρ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    have hxy : x ≠ y := fun he => h (by subst he; simp [Term.fv])
    exact REnv.get_write_other bv ρ x v hxy
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]
  | not t ih => simp only [Term.interp, ih h]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]

theorem Formula.interp_write_fresh (φ : Formula)
    (x : EVar) (v : Val) (ρ : REnv)
    (hfv : x ∉ φ.fv) (hnamed : x ∉ φ.named) :
    Formula.interp (ρ.write x v) φ ↔ Formula.interp ρ φ := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  induction φ generalizing ρ with
  | tt => simp [Formula.interp]
  | ff => simp [Formula.interp]
  | eqI t₁ t₂ | eqB t₁ t₂ | leqI t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp,
      Term.interp_write_fresh t₁ x v ρ (not_mem_l _ _ _ hfv),
      Term.interp_write_fresh t₂ x v ρ (not_mem_r _ _ _ hfv)]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    grind
  | not φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    exact not_congr (ih ρ hfv hnamed)
  | exI y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := fun hmem => hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    refine exists_congr (fun n => ?_)
    rw [← REnv.write_update_comm .int ρ y n x v hxy]
    exact ih (ρ.update .int y n) hxf hxn
  | exB y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := fun hmem => hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    refine exists_congr (fun b => ?_)
    rw [← REnv.write_update_comm .bool ρ y b x v hxy]
    exact ih (ρ.update .bool y b) hxf hxn
  | allI y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := fun hmem => hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    refine forall_congr' (fun n => ?_)
    rw [← REnv.write_update_comm .int ρ y n x v hxy]
    exact ih (ρ.update .int y n) hxf hxn
  | allB y φ ih =>
    simp only [Formula.fv, Formula.named] at hfv hnamed
    simp only [Formula.interp]
    have hxy : x ≠ y := fun h => hnamed (List.mem_cons.mpr (Or.inl h))
    have hxn : x ∉ φ.named := fun h => hnamed (List.mem_cons.mpr (Or.inr h))
    have hxf : x ∉ φ.fv := fun hmem => hfv (List.mem_filter.mpr ⟨hmem, by simp [hxy]⟩)
    refine forall_congr' (fun b => ?_)
    rw [← REnv.write_update_comm .bool ρ y b x v hxy]
    exact ih (ρ.update .bool y b) hxf hxn

end STLC
