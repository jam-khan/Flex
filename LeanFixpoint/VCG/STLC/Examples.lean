import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.Tactic.Hoist

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

def int_k (k : Int → Prop)  : Ty := .refine .int ⟨fun _ ν => k ν⟩

def exId : Exp := .lam "x" (.var "x")
def ty_k (k1 : Int → Prop) : Ty := Ty.arrow "x" (int_k k1) (int_k k1)


@[qualif]
def Gt0 (v : Int) : Prop :=
  v > 0

example : ∃ k, Check [] (.letin "z" (.const 99) (.app (.ann exId (ty_k k)) (.var "z"))) Pos := by
  under_exists =>
    apply check_sound
    · simp [exId, Pos, ty_k, int_k, check, synth]
      repeat (first | unfold check | unfold synth)
      simp ; rfl
    focus simp
  solve_fixpoint

-- example : ∃ k, topVC [] (.app (.ann exId (ty_k k)) (.const 99)) Pos := by
--   refine ⟨?_, ?_⟩
--   rotate_left 1
--   unfold topVC check
--   simp [topVC, check, synth, implyBind, exId, Pos, ty_k, int_k]

-- Check [] (.app (.ann exId (ty_k k)) (.const 99)) Pos := by
--   refine ⟨?_, ?_⟩
--   rotate_left 1
--   apply check_sound
--   ·

-- IntR x k := .refine .int (fun r v => k (r x) v)

-- ty_k x k := .arrow x IntT (IntR x k)

def IntR (x : String) (k : Int → Int → Prop) : Ty := .refine .int ⟨fun ρ v => k (ρ x) v⟩
def ty_xk (x : String) (k : Int → Int → Prop) : Ty := .arrow "x" TT (IntR x k)

example : ∃ k, Check [] (.letin "z" (.const 99) (.app (.ann exId (ty_xk "x" k)) (.var "z"))) (.refine .int ⟨fun _ v => v = 99⟩) := by
  under_exists =>
    apply check_sound
    · simp [exId, ty_xk, TT, IntR]
      repeat (first | unfold check | unfold synth)
      simp ; rfl
    focus simp
  solve_fixpoint

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
  intros ; assumption

-- let z = 5 in z is declaratively typeable at Pos.
example : Hastype [] ex3Exp ex3Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, implyBind, ex3Exp, ex3Ty, Pos, prim]
