/-! # While-Language AST (Shallow Embedding)

  Expressions and guards are native Lean functions over `State`,
  so VCs come out as clean Lean Props with no custom AST to evaluate.
-/

abbrev CVar := String

abbrev State := CVar → Int

def State.update (s : State) (x : CVar) (v : Int) : State :=
  fun y => if x == y then v else s y

notation s "[" x " ↦ " v "]" => State.update s x v

def State.empty : State := fun _ => 0
notation "∅" => State.empty

inductive Cmd where
  | skip   : Cmd
  | assign : CVar → (State → Int) → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : (State → Bool) → Cmd → Cmd → Cmd
  | cwhile : (State → Bool) → Cmd → Cmd
