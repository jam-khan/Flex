import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.Tactic.SolveFusion

open STLC

/-! ## Refinement helpers -/

def TT   : Ty := .refine .int ⟨fun _ _ => True⟩
def Pos  : Ty := .refine .int ⟨fun _ ν => ν > 0⟩
def NatR : Ty := .refine .int ⟨fun _ ν => 0 ≤ ν⟩    -- was Nat

/-! ## Example 1: 5 ⇐ {ν : ν > 0} -/

def ex1Exp : Exp := .const 5
def ex1Ty  : Ty  := Pos

example : topVC [] ex1Exp ex1Ty := by
  simp only [topVC, check, synth, sub, ex1Exp, ex1Ty, Pos, prim]
  solve_fusion

/-! ## Example 2: identity (λx. x) ⇐ x:Pos → Pos -/

def ex2Exp : Exp := .lam "x" (.var "x")
def ex2Ty  : Ty  := .arrow "x" Pos Pos

example : topVC [] ex2Exp ex2Ty := by
  simp [topVC, check, synth, implyBind, ex2Exp, ex2Ty, Pos]

/-! ## Example 3: let z = 5 in z ⇐ Pos -/

def ex3Exp : Exp := .letin "z" (.const 5) (.var "z")
def ex3Ty  : Ty  := Pos

example : topVC [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, implyBind, ex3Exp, ex3Ty, Pos, prim]

/-! ## Declarative-side examples

  Same programs as above, but stated as derivations of the new declarative
  `Hastype` judgement. Each one routes through `topVC_decl_sound`,
  reusing the `topVC` proof above. -/

-- Identity (λ x. x) is declaratively typeable at x:Pos → Pos.
example : Hastype [] ex2Exp ex2Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, implyBind, ex2Exp, ex2Ty, Pos]

-- let z = 5 in z is declaratively typeable at Pos.
example : Hastype [] ex3Exp ex3Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, implyBind, ex3Exp, ex3Ty, Pos, prim]
