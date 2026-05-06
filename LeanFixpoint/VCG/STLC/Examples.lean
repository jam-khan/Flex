import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.VCG.STLC.MakeHornUnderK

open STLC

/-! ## Refinement helpers -/

abbrev TT   : Ty := .refine .int ⟨fun _ _ => True⟩
abbrev Pos  : Ty := .refine .int ⟨fun _ ν => ν > 0⟩
def NatR : Ty := .refine .int ⟨fun _ ν => 0 ≤ ν⟩    -- was Nat

/-! ## Example 1: 5 ⇐ {ν : ν > 0} -/

def ex1Exp : Exp := .iconst 5
def ex1Ty  : Ty  := Pos

example : topVC [] ex1Exp ex1Ty := by
  simp only [topVC, check, synth, sub, ex1Exp, ex1Ty, Pos, prim]
  solve_fixpoint

/-! ## Example 2: identity (λx. x) ⇐ x:Pos → Pos -/

def ex2Exp : Exp := .lam "x" (.var "x")
def ex2Ty  : Ty  := .arrow "x" Pos Pos

example : topVC [] ex2Exp ex2Ty := by
  simp [topVC, check, synth, implyBind, ex2Exp, ex2Ty, Pos]
  solve_fixpoint

/-! ## Example 3: let z = 5 in z ⇐ Pos -/

def ex3Exp : Exp := .letin "z" (.iconst 5) (.var "z")
def ex3Ty  : Ty  := Pos

abbrev int_k (k : Int → Prop)  : Ty := .refine .int ⟨fun _ ν => k ν⟩

abbrev exId : Exp := .lam "x" (.var "x")
abbrev ty_k (k1 : Int → Prop) : Ty := Ty.arrow "x" (int_k k1) (int_k k1)

@[qualif]
def Gt0 (v : Int) : Prop :=
  v > 0

example : ∃ k, Check [] (.letin "z" (.iconst 99) (.app (.ann exId (ty_k k)) (.var "z"))) Pos := by
  make_horn_under_k
  solve_fixpoint

abbrev IntN (n : Int) : Ty := .refine .int ⟨fun _ v => v = n⟩
abbrev IntR (x : String) (k : Int → Int → Prop) : Ty := .refine .int ⟨fun ρ v => k (ρ.ints x) v⟩
abbrev ty_xk (x : String) (k : Int → Int → Prop) : Ty := .arrow "x" TT (IntR x k)

example : ∃ k, Check [] (.letin "z" (.iconst 99) (.app (.ann exId (ty_xk "x" k)) (.var "z"))) (IntN 99) := by
  make_horn_under_k
  solve_fixpoint

example : topVC [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, implyBind, ex3Exp, ex3Ty, Pos, prim]

abbrev exGt : Exp := .lam "x" (.lam "y" (.not (.leq (.var "x") (.var "y"))))
abbrev tyGt : Ty := Ty.arrow "x" TT (Ty.arrow "y" TT (.refine .bool ⟨fun ρ v => v = (ρ.ints "x" > ρ.ints "y")⟩))

example : topVC [] exGt tyGt := by
  simp [topVC, check]

/-! ## Declarative-side examples

  Same programs as above, but stated as derivations of the new declarative
  `Hastype` judgement. Each one routes through `topVC_decl_sound`,
  reusing the `topVC` proof above. -/

-- Identity (λ x. x) is declaratively typeable at x:Pos → Pos.
example : Hastype [] ex2Exp ex2Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, implyBind, ex2Exp, ex2Ty, Pos]
  intros ; assumption

-- let z = 5 in z is declaratively typeable at Pos.
example : Hastype [] ex3Exp ex3Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, implyBind, ex3Exp, ex3Ty, Pos, prim]
