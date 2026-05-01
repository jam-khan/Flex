
namespace STLC

abbrev EVar := String
abbrev REnv := EVar → Int
@[simp]
def REnv.empty : REnv := fun _ => 0
@[simp]
def REnv.update (ρ : REnv) (x : EVar) (v : Int) : REnv :=
  fun y => if x == y then v else ρ y
notation ρ "[" x " ↦ " v "]" => REnv.update ρ x v

inductive Const where
  | int : Int → Const
  deriving Repr, DecidableEq

inductive Base where
  | int : Base
  deriving Repr, DecidableEq

@[reducible]
def Base.interp : Base → Type
  | .int => Int

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
  ⟨fun ρ v => r.pred (fun z => if z == x then ρ y else ρ z) v⟩

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
  | const : Int → Exp               -- c
  | var   : EVar  → Exp             -- x
  | letin : EVar  → Exp → Exp → Exp -- let x = e₁ in e₂
  | lam   : EVar  → Exp → Exp       -- λ x. e
  | app   : Exp   → Exp → Exp       -- e x
  | ann   : Exp   → Ty  → Exp       -- e:t

@[simp]
abbrev TEnv := List (EVar × Ty)

end STLC
