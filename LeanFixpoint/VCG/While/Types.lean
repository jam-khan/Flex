/-! # While-Language AST (Shallow Embedding)

  Expressions and guards are native Lean functions over `State`,
  so VCs come out as clean Lean Props with no custom AST to evaluate.
-/

abbrev CVar := String

abbrev State := CVar → Int

@[simp]
def State.update (s : State) (x : CVar) (v : Int) : State :=
  fun y => if x == y then v else s y

notation s "[" x " ↦ " v "]" => State.update s x v

@[simp]
def State.empty : State := fun _ => 0
notation "∅" => State.empty

inductive Cmd where
  | skip   : Cmd
  | assign : CVar → (State → Int) → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : (State → Bool) → Cmd → Cmd → Cmd
  | cwhile : (State → Bool) → Cmd → Cmd

/-- Collect all assignment-target variable names in first-appearance order. -/
def Cmd.assignedVars : Cmd → List CVar
  | .skip        => []
  | .assign x _  => [x]
  | .seq c₁ c₂   => (c₁.assignedVars ++ c₂.assignedVars).eraseDups
  | .ite _ c₁ c₂ => (c₁.assignedVars ++ c₂.assignedVars).eraseDups
  | .cwhile _ c  => c.assignedVars

/-- Curried n-ary predicate type: `NaryProp n = Int → Int → ... → Prop` (n times). -/
@[reducible] def NaryProp : Nat → Type
  | 0     => Prop
  | n + 1 => Int → NaryProp n

/-- Apply an n-ary predicate to the values of `xs` in a state, yielding a `Prop`. -/
@[simp] def applyNary : (xs : List CVar) → NaryProp xs.length → State → Prop
  | [],      p, _ => p
  | x :: xs, f, s => applyNary xs (f (s x)) s
