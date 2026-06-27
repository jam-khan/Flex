
namespace STLC

/-! # STLC Syntax (locally nameless + deeply embedded refinements)

  Layout:

  1. **Variables, bases, runtime envs** — `EVar`, `Base`, `REnv`.
  2. **Deep-embedded refinement language** — `Term`, `Formula`, `Refinement`.
     ν is a distinguished free name (`nuName`); no LN inside formulas.
  3. **Types (LN)** — `Ty`. `arrow s t` carries no binder name; `t` is a body
     with `BVar 0` standing for the function argument.
  4. **Expressions (LN)** — `Exp`. Binding forms (`lam`, `letin`) carry no
     binder name; the body has `BVar 0` for the innermost binder.

  All substitution / opening / closing / freshness machinery lives in
  `Substitution.lean`. This file declares data only.
-/

abbrev EVar := String

inductive Const where
  | int : Int → Const
  deriving Repr, DecidableEq

inductive Base where
  | int  : Base
  | bool : Base
  deriving Repr, DecidableEq

@[simp, reducible]
def Base.interp : Base → Type
  | .int  => Int
  | .bool => Bool

/-- Runtime environment: separate total maps for integer and boolean variables.
    Keeping the two components apart means lookups always return a concrete type
    (`Int` or `Bool`) without any `Val` wrapper or coercion. -/
@[ext]
structure REnv where
  ints  : EVar → Int
  bools : EVar → Bool

@[simp] def REnv.empty : REnv := ⟨fun _ => 0, fun _ => false⟩

/-- Look up the `b`-typed value of variable `x` in `ρ`. -/
@[simp, reducible]
def REnv.get (b : Base) (ρ : REnv) (x : EVar) : b.interp :=
  match b with
  | .int  => ρ.ints x
  | .bool => ρ.bools x

/-- Update the `b`-typed slot for `x` in `ρ` to `v`. -/
@[simp, reducible]
def REnv.update (b : Base) (ρ : REnv) (x : EVar) (v : b.interp) : REnv :=
  match b with
  | .int  => { ρ with ints  := fun y => if x == y then v else ρ.ints y }
  | .bool => { ρ with bools := fun y => if x == y then v else ρ.bools y }

/-! ## Deep-embedded refinement language

  The refinement-side DSL is a first-order language over `REnv` slots plus the
  distinguished value ν. Refinements never nest ν, so we keep ν as a reserved
  free name (`nuName`) rather than LN-binding it.

  Existentials inside `Formula` are *named*, which is fine because they appear
  only in derived refinements (e.g. `not_` / `and_`) and are well-scoped by
  construction at every introduction site.
-/

/-- Reserved name for ν, the value being refined. Never used as a regular
    program variable. The base of ν is fixed by the enclosing `Refinement b`. -/
def nuName : EVar := "ν"

/-- Base-indexed first-order terms over `REnv` slots ∪ {ν} ∪ Ty-bound vars.

    `Term.fvar b nuName` denotes ν of base `b`. Other `fvar` names refer to
    slots in `REnv` (looked up with `REnv.get`).

    `Term.bvar b k` is a de Bruijn index referring to the k-th enclosing
    `Ty.arrow` binder (k = 0 is the innermost). The base `b` must match the
    binder's domain refinement base; ill-base BVars in well-formed types
    never appear. -/
inductive Term : Base → Type where
  | const : (b : Base) → b.interp → Term b
  | bvar  : (b : Base) → Nat → Term b
  | fvar  : (b : Base) → EVar → Term b
  | add   : Term .int  → Term .int  → Term .int
  | not   : Term .bool → Term .bool
  | and   : Term .bool → Term .bool → Term .bool
-- NOTE: no cross-base constructors (e.g. `leq : Term .int → Term .int → Term .bool`).
-- Keeping each `Term` homogeneous in its base means an `REnv` update at one base
-- can never affect a term of another base. Cross-base relations go in
-- `Formula` (e.g. `Formula.leqI`).

/-- First-order formulas over `Term`s.

    Logical connectives are explicit (no metalevel `Prop` mixing). Existentials
    are named — each `exI x φ` / `exB x φ` binds `x` inside `φ`. Substitution
    on Formula respects the binder (skips substitution into shadowed bodies). -/
inductive Formula where
  | tt    : Formula
  | ff    : Formula
  | eqI   : Term .int  → Term .int  → Formula
  | eqB   : Term .bool → Term .bool → Formula
  | leqI  : Term .int  → Term .int  → Formula
  | and   : Formula → Formula → Formula
  | or    : Formula → Formula → Formula
  | not   : Formula → Formula
  | imp   : Formula → Formula → Formula
  | exI   : EVar → Formula → Formula   -- ∃ x : Int.  φ
  | exB   : EVar → Formula → Formula   -- ∃ x : Bool. φ
  | allI  : EVar → Formula → Formula   -- ∀ x : Int.  φ
  | allB  : EVar → Formula → Formula   -- ∀ x : Bool. φ

/-- A refinement, one stratification level *above* `Formula`: either a
    kvar-FREE `Formula` (whose free `nuName` denotes the refined value), or a
    single κ-application `κ(t₁, …, tₙ)`. Keeping κ here rather than inside
    `Formula` makes a refinement *atomic* — a constraint XOR one positive κ
    atom — so κ can never be negated/disjoined/nested. Every VC the generator
    emits then has the shape `(⋀ refinement-hyps) → refinement-head`, i.e. it is
    a Constrained Horn Clause by construction. `Refinement.interp` (in
    `Substitution.lean`) is the only interpretation that needs the κ-assignment.
    (The κ name is an `EVar`; see `KVar` below, defined to be `EVar`.) -/
inductive Refinement (b : Base) where
  | fmla : Formula → Refinement b
  | kapp : EVar → List (Σ b : Base, Term b) → Refinement b

/-! ## κ-assignments

  A `KVar` is a name for an *uninterpreted* predicate symbol (a "κ" in the
  refinement-types literature). The solver picks `KEnv`-values that satisfy
  the VCs; the user existentially binds over `KEnv` to invoke the solver. -/

abbrev KVar : Type := EVar

/-- κ-assignment: maps each `KVar` to a Lean predicate over its (heterogeneous)
    base-typed argument list. -/
abbrev KEnv : Type := KVar → List (Σ b : Base, b.interp) → Prop

/-! ## KEnv construction helpers

  `liftK1` / `liftK2` lift curried predicates into the heterogeneous-list form
  expected by `KEnv`. `mkKEnv` builds a `KEnv` from a finite name→predicate
  list, defaulting to `True` for unmentioned keys. `exists_kenv_curried` is
  the sufficiency lemma used by the `intro_kenv` tactic to replace
  `∃ κ : KEnv, P κ` with individual curried existentials. -/

def liftK1 (p : Int → Prop) : List (Σ b : Base, b.interp) → Prop
  | [⟨.int, v⟩] => p v
  | _            => True

def liftK2 (p : Int → Int → Prop) : List (Σ b : Base, b.interp) → Prop
  | [⟨.int, x⟩, ⟨.int, y⟩] => p x y
  | _                        => True

def mkKEnv (ks : List (KVar × (List (Σ b : Base, b.interp) → Prop))) : KEnv :=
  fun name => (ks.lookup name).getD (fun _ => True)

theorem exists_kenv_curried {P : KEnv → Prop}
    (ks : List (KVar × (List (Σ b : Base, b.interp) → Prop)))
    (h : P (mkKEnv ks)) : ∃ κ : KEnv, P κ :=
  ⟨mkKEnv ks, h⟩

/-! ## Types — locally nameless

  `arrow s t`: the codomain `t` is a *body* with `BVar 0` representing the
  function argument. There are NO binder names on `arrow`.

  `refine b r` is non-binding at the `Ty` level (ν is internal to the
  `Refinement`).
-/

inductive Ty where
  | refine : (b : Base) → Refinement b → Ty
  | arrow  : Ty → Ty → Ty

/-! ## Expressions — locally nameless

  Every binding form (`lam`, `letin`) carries no `EVar`. The body is an `Exp`
  with `BVar 0` representing the innermost binder; outer binders use `BVar 1`,
  etc. Free variables remain named via `fvar`.
-/

inductive Exp where
  | bvar   : Nat  → Exp                 -- de Bruijn index for bound vars
  | fvar   : EVar → Exp                 -- named free var
  | iconst : Int  → Exp
  | bconst : Bool → Exp
  | lam    : Exp → Exp                  -- body has BVar 0 = parameter
  | letin  : Exp → Exp → Exp            -- letin e₁ e₂; e₂ has BVar 0 = bound name
  | app    : Exp → Exp → Exp
  | ann    : Exp → Ty  → Exp
  | and    : Exp → Exp → Exp
  | not    : Exp → Exp
  | leq    : Exp → Exp → Exp
  | ite    : Exp → Exp → Exp → Exp
  | add    : Exp → Exp → Exp

/-- Typing context: a list of free-name × type pairs. Names are unique by
    convention (typing rules enforce via cofinite quantification — see
    `Declarative.lean` / `Typing.lean`). -/
@[simp]
abbrev TEnv := List (EVar × Ty)

/-- Get all free names declared in a typing context. -/
def TEnv.dom : TEnv → List EVar
  | []          => []
  | (x, _) :: Γ => x :: TEnv.dom Γ

/-! ## Runtime values

  Locally nameless closures: `clos body` carries an `Exp` body whose `BVar 0`
  represents the parameter. Operations on `Val` (`fv`, `lc`, etc.) live in
  `Substitution.lean` alongside the corresponding `Exp` operations.
-/

inductive Val where
  | iconst : Int  → Val
  | bconst : Bool → Val
  | clos   : Exp  → Val

/-- Inject a value into the syntax (used by big-step `lam` and `Exp.openVal`). -/
@[simp] def Val.toExp : Val → Exp
  | .iconst n   => .iconst n
  | .bconst b   => .bconst b
  | .clos body  => .lam body

end STLC
