
namespace STLC

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

structure Refinement (b : Base) where
  int_fv  : List EVar
  bool_fv : List EVar
  pred    : REnv → b.interp → Prop
  ext     : ∀ {ρ₁ ρ₂ : REnv} {v : b.interp},
              (∀ y ∈ int_fv,  ρ₁.ints y  = ρ₂.ints y)  →
              (∀ y ∈ bool_fv, ρ₁.bools y = ρ₂.bools y) →
              (pred ρ₁ v ↔ pred ρ₂ v)

inductive Ty where
  | refine : (b : Base) → Refinement b → Ty   -- {ν : b | p (ρ ν)}
  | arrow  : EVar → Ty → Ty → Ty              -- x:s → t

-- NOTE: The current setup uses a "same-binder" convention to avoid alpha
-- renaming machinery: typing rules introduce the same binder name in the term
-- and in the type context extension, and the user must alpha-rename inputs
-- accordingly. ALL substitution / renaming operations and lemmas live in
-- `Substitution.lean`. When the same-binder restriction is lifted (locally-
-- nameless or freshness-aware named binders), `Substitution.lean` is the file
-- that grows; this file (`Syntax.lean`) only declares the data types.

inductive Exp where
  | iconst : Int  → Exp               -- integer literal
  | bconst : Bool → Exp               -- boolean literal
  | var    : EVar  → Exp              -- x
  | letin  : EVar  → Exp → Exp → Exp -- let x = e₁ in e₂
  | lam    : EVar  → Exp → Exp       -- λ x. e
  | app    : Exp   → Exp → Exp       -- e x
  | ann    : Exp   → Ty  → Exp       -- e:t
  | and    : Exp   → Exp → Exp       -- e₁ ∧ e₂
  | not    : Exp   → Exp             -- ¬ e
  | leq    : Exp   → Exp → Exp       -- e₁ ≤ e₂
  | ite    : Exp   → Exp → Exp → Exp -- if e₀ then e₁ else e₂
  | add    : Exp   → Exp → Exp       -- e₁ + e₂

@[simp]
abbrev TEnv := List (EVar × Ty)

end STLC
