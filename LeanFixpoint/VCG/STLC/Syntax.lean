
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

/-- Redirect lookups of `x` to `y` in both components of an env.
    Used by `Refinement.rename` to implement variable renaming. -/
@[simp]
def REnv.redirect (ρ : REnv) (x y : EVar) : REnv :=
  { ints  := fun z => if z == x then ρ.ints  y else ρ.ints  z
  , bools := fun z => if z == x then ρ.bools y else ρ.bools z }

structure Refinement (b : Base) where
  pred : REnv → b.interp → Prop

inductive Ty where
  | refine : (b : Base) → Refinement b → Ty   -- {ν : b | p (ρ ν)}
  | arrow  : EVar → Ty → Ty → Ty              -- x:s → t

-- NOTE: BELOW IS A HACK TO AVOID NAME ISSUES
-- IT MUST BE HANDLED PROPERLY WHEN MECHANIZING
-- META-THEORY, Either by LOCALLY NAMELESS or
-- SUBSTITUTION (PAINFUL) LEMMAS
/-- Redirect ρ-lookups of `x` to lookups of `y` inside a refinement. -/
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
