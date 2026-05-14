import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.VCG.STLC.MakeHornUnderK

open STLC

/-! ## Refinement helpers -/

abbrev TT   : Ty := .refine .int { int_fv := [], bool_fv := [], pred := fun _ _ => True, ext := fun _ _ => Iff.rfl }
abbrev Pos  : Ty := .refine .int { int_fv := [], bool_fv := [], pred := fun _ ν => ν > 0, ext := fun _ _ => Iff.rfl }
def NatR : Ty := .refine .int { int_fv := [], bool_fv := [], pred := fun _ ν => 0 ≤ ν, ext := fun _ _ => Iff.rfl }

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

abbrev int_k (k : Int → Prop)  : Ty := .refine .int { int_fv := [], bool_fv := [], pred := fun _ ν => k ν, ext := fun _ _ => Iff.rfl }

abbrev exId : Exp := .lam "x" (.var "x")
abbrev ty_k (k1 : Int → Prop) : Ty := Ty.arrow "x" (int_k k1) (int_k k1)

@[qualif]
def Gt0 (v : Int) : Prop :=
  v > 0

example : ∃ k, Check [] (.letin "z" (.iconst 99) (.app (.ann exId (ty_k k)) (.var "z"))) Pos := by
  make_horn_under_k [List.lookup]
  solve_fixpoint

abbrev IntN (n : Int) : Ty := .refine .int { int_fv := [], bool_fv := [], pred := fun _ v => v = n, ext := fun _ _ => Iff.rfl }
abbrev IntR (x : String) (k : Int → Int → Prop) : Ty := .refine .int { int_fv := [x], bool_fv := [],
  pred := fun ρ v => k (ρ.ints x) v,
  ext := fun h_int _h_bool => by simp [h_int x (by simp)] }
abbrev ty_xk (x : String) (k : Int → Int → Prop) : Ty := .arrow "x" TT (IntR x k)

example : ∃ k, Check [] (.letin "z" (.iconst 99) (.app (.ann exId (ty_xk "x" k)) (.var "z"))) (IntN 99) := by
  make_horn_under_k [List.lookup]
  solve_fixpoint

example : topVC [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, implyBind, ex3Exp, ex3Ty, Pos, prim]

abbrev exGt : Exp := .lam "x" (.lam "y" (.not (.leq (.var "x") (.var "y"))))
abbrev tyGt : Ty := Ty.arrow "x" TT (Ty.arrow "y" TT (.refine .bool { int_fv := ["x", "y"], bool_fv := [],
  pred := fun ρ v => v = (ρ.ints "x" > ρ.ints "y"),
  ext := by intro ρ₁ ρ₂ v h_int _h_bool
            have hx := h_int "x" (by simp)
            have hy := h_int "y" (by simp)
            simp [hx, hy] }))

example : topVC [] exGt tyGt := by
  simp [topVC, check, synth, List.lookup]


abbrev exMax : Exp :=
  .lam "x"
    (.lam "y"
      (.letin "c"
        (.leq (.var "x") (.var "y"))
        (.ite
          (.var "c")
          (.var "y")
          (.var "x")
        )
      )
    )

abbrev IntK (k : Int → Prop) : Ty := .refine .int { int_fv := [], bool_fv := [], pred := fun _ v => k v, ext := fun _ _ => Iff.rfl }

example : ∃ (k1 k2 k3 : Int → Prop), Check [] (
  .letin "a"
    (.iconst 99)
    (.letin "b"
      (.iconst 100)
      (.app (.app (.ann exMax (.arrow "x" (IntK k1) (.arrow "y" (IntK k2) (.refine .int { int_fv := [], bool_fv := [], pred := fun _ v => k3 v, ext := fun _ _ => Iff.rfl })))) (.var "a")) (.var "b"))
    )
  ) (.refine .int { int_fv := [], bool_fv := [], pred := fun _ v => v = 100 ∨ v = 99, ext := fun _ _ => Iff.rfl }) := by
  make_horn_under_k [List.lookup]
  solve_fixpoint

def exAddExp : Exp :=
  .letin "a" (.iconst 3)
    (.letin "b" (.iconst 4)
      (.add (.var "a") (.var "b")))

def exAddTy : Ty := IntN 7

example : topVC [] exAddExp exAddTy := by
  simp [topVC, check, synth, implyBind, exAddExp, exAddTy, prim, List.lookup]

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
