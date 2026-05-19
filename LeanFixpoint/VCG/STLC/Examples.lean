import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative
import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.VCG.STLC.MakeHornUnderK
import LeanFixpoint.Tactic.SolveFixpoint

open STLC

/-! # Examples — full port of pre-refactor suite, LN + deep Formula + κ

  All examples re-stated under:
  - LN binders (`Exp.lam (.bvar 0)` etc.)
  - Deep `Formula` refinements
  - κ-aware judgements (`topVC κ`, `Check κ`, `Hastype κ`)

  Proofs preserve the *spirit* of the original tactics:
  `simp + solve_fixpoint`, `make_horn_under_k + solve_fixpoint`,
  `topVC_decl_sound + simp + intros`.

  Where the chain runs but goes through `check_sound` (Stage 13 to prove),
  proofs are **sorry-tainted** but the tactic invocations are real.
-/

/-! ## Refinement helpers -/

/-- `TT = {ν : Int | True}`. -/
abbrev TT  : Ty := .refine .int ⟨.tt⟩

/-- `Pos = {ν : Int | 1 ≤ ν}` (integer `ν > 0`). -/
abbrev Pos : Ty := .refine .int ⟨.leqI (.const .int 1) (.fvar .int nuName)⟩

/-- `NatR = {ν : Int | 0 ≤ ν}`. -/
def NatR : Ty := .refine .int ⟨.leqI (.const .int 0) (.fvar .int nuName)⟩

/-- `IntN n = {ν : Int | ν = n}`. -/
abbrev IntN (n : Int) : Ty :=
  .refine .int ⟨.eqI (.fvar .int nuName) (.const .int n)⟩

/-- κ-refinement on int: `{ν : Int | k(ν)}` for κ-symbol `k`. -/
abbrev IntK (k : STLC.KVar) : Ty :=
  .refine .int ⟨.kapp k [⟨.int, .fvar .int nuName⟩]⟩

/-- κ-refinement on int referencing both an outer variable and ν: `{ν | k(x, ν)}`. -/
abbrev IntR (k : STLC.KVar) : Ty :=
  .refine .int ⟨.kapp k [⟨.int, .bvar .int 0⟩, ⟨.int, .fvar .int nuName⟩]⟩

/-- Identity function under LN. -/
abbrev exId : Exp := .lam (.bvar 0)

/-- Function type for identity at `IntK k → IntK k`. -/
abbrev ty_k (k : STLC.KVar) : Ty := .arrow (IntK k) (IntK k)

/-- Function type for `TT → IntR x k`. -/
abbrev ty_xk (k : STLC.KVar) : Ty := .arrow TT (IntR k)

/-! ## Example 1: `5 ⇐ Pos` -/

def ex1Exp : Exp := .iconst 5
def ex1Ty  : Ty  := Pos

example (κ : KEnv) : topVC κ [] ex1Exp ex1Ty := by
  simp only [topVC, check, synth, sub, ex1Exp, ex1Ty, Pos, prim,
             Refinement.interp, Formula.interp, Term.interp, REnv.get]
  solve_fixpoint

/-! ## Example 2: identity `λx. x ⇐ Pos → Pos` -/

def ex2Exp : Exp := exId
def ex2Ty  : Ty  := .arrow Pos Pos

set_option maxHeartbeats 800000 in
example (κ : KEnv) : topVC κ [] ex2Exp ex2Ty := by
  simp [topVC, check, synth, sub, implyBind, ex2Exp, exId, ex2Ty, Pos, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar,
        Term.openBVar]
  intros; assumption

/-! ## Example 3: `let z = 5 in z ⇐ Pos` -/

def ex3Exp : Exp := .letin (.iconst 5) (.bvar 0)
def ex3Ty  : Ty  := Pos

example (κ : KEnv) : topVC κ [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, sub, implyBind, ex3Exp, ex3Ty, Pos, prim, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar]

/-! ## κ-example with `ty_k`: `let z = 99 in (λx. x : IntK k → IntK k) z ⇐ Pos`

  Original used `make_horn_under_k [List.lookup]; solve_fixpoint`.
  Here the macro is sorry-tainted via `check_sound` (Stage 13). -/

attribute [simp] check synth sub EVar.fresh implyBind prim self Refinement.interp Formula.interp TEnv.dom
attribute [simp] Term.interp REnv.get Exp.openVar Ty.openVar Exp.fv Refinement.fv Formula.fv Term.fv Ty.fv
attribute [simp] Refinement.openBVar Formula.openBVar Term.openBVar nuName String.length EVar.maxLen
attribute [simp] List.lookup

@[qualif]
def Ge1 (i : Int) : Prop := 1 ≤ i

example :
    ∃ κ : KEnv,
      Check κ []
        (.letin (.iconst 99) (.app (.ann exId (ty_k "k")) (.bvar 0)))
        Pos := by
  under_exists =>
    apply check_sound
    simp ; rfl
    simp
  intro_kenv
  simp [mkKEnv, liftK1]
  solve_fixpoint

/-! ## κ-example with `ty_xk`: same shape, output type `IntN 99` -/

example :
    ∃ κ : KEnv,
      Check κ []
        (.letin (.iconst 99) (.app (.ann exId (ty_xk "k")) (.bvar 0)))
        (IntN 99) := by
    under_exists =>
      apply check_sound
      simp ; rfl
      simp
    intro_kenv
    simp [mkKEnv, List.lookup, liftK2]
    solve_fixpoint

-- /-! ## Example 3 again: prove `topVC` without solver -/

example (κ : KEnv) : topVC κ [] ex3Exp ex3Ty := by
  simp [topVC, ex3Exp, ex3Ty]

/-! ## `exGt`: `λ x. λ y. let c = x ≤ y in ¬c  ⇐  TT → TT → {ν | ν = true ↔ x > y}`

  Uses `not_var`: the letin names the leq result as a fvar, then `.not (.bvar 0)` opens
  to `.not (.fvar c)` which matches the `not_var` rule. -/

abbrev exGt : Exp :=
  .lam (.lam (.letin (.leq (.bvar 1) (.bvar 0)) (.not (.bvar 0))))

/-- `ν = true ↔ ¬(x ≤ y)`, using bvars for the two arrow-bound ints. -/
abbrev tyGt : Ty :=
  .arrow TT (.arrow TT
    (.refine .bool ⟨.and
      (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
            (.not (.leqI (.bvar .int 1) (.bvar .int 0))))
      (.imp (.not (.leqI (.bvar .int 1) (.bvar .int 0)))
            (.eqB (.fvar .bool nuName) (.const .bool true)))⟩))

example (κ : KEnv) : topVC κ [] exGt tyGt := by
  simp [topVC, exGt, tyGt]

/-! ## `exEq`: `λ x. λ y. let u = x ≤ y in let v = y ≤ x in u ∧ v`
                                             `⇐  TT → TT → {ν | ν = true ↔ x = y}`

  Uses `and_var`: both letin-bound booleans become fvars, then `.and (.bvar 1) (.bvar 0)`
  opens to `.and (.fvar u) (.fvar v)` which matches the `and_var` rule. -/

abbrev exEq : Exp :=
  .lam (.lam
    (.letin (.leq (.bvar 1) (.bvar 0))       -- let u = x ≤ y
      (.letin (.leq (.bvar 1) (.bvar 2))     -- let v = y ≤ x
        (.and (.bvar 1) (.bvar 0)))))         -- u ∧ v

/-- `ν = true ↔ (x ≤ y ∧ y ≤ x)`, i.e. x = y. -/
abbrev tyEq : Ty :=
  .arrow TT (.arrow TT
    (.refine .bool ⟨.and
      (.imp (.eqB (.fvar .bool nuName) (.const .bool true))
            (.and (.leqI (.bvar .int 1) (.bvar .int 0))
                  (.leqI (.bvar .int 0) (.bvar .int 1))))
      (.imp (.and (.leqI (.bvar .int 1) (.bvar .int 0))
                  (.leqI (.bvar .int 0) (.bvar .int 1)))
            (.eqB (.fvar .bool nuName) (.const .bool true)))⟩))

example (κ : KEnv) : topVC κ [] exEq tyEq := by
  simp [topVC, exEq, tyEq]
  solve_fixpoint

/-! ## `exMax`: `λx. λy. let c = x ≤ y in if c then y else x`

  Demonstrates ite + leq + cofinite let nested inside two cofinite λs. -/

abbrev exMax : Exp :=
  .lam       -- λ x.
    (.lam    -- λ y.
      (.letin (.leq (.bvar 1) (.bvar 0))    -- let c = x ≤ y
        (.ite (.bvar 0)                      -- in if c
              (.bvar 1)                      -- then y
              (.bvar 2))))                   -- else x

/-! ## κ flagship: `let a = 99 in let b = 100 in exMax a b ⇐ {ν | ν = 100 ∨ ν = 99}` -/

example :
    ∃ κ : KEnv,
      Check κ []
        (.letin (.iconst 99)
          (.letin (.iconst 100)
            (.app (.app (.ann exMax
                          (.arrow (IntK "k1")
                            (.arrow (IntK "k2") (IntK "k3"))))
                        (.bvar 1)) (.bvar 0))))
        (.refine .int ⟨.or
          (.eqI (.fvar .int nuName) (.const .int 100))
          (.eqI (.fvar .int nuName) (.const .int  99))⟩) := by
  under_exists =>
    apply check_sound
    simp ; rfl
    simp
  intro_kenv
  simp [mkKEnv, liftK1]
  solve_fixpoint

/-! ## Arithmetic: `let a = 3 in let b = 4 in a + b ⇐ IntN 7` -/

def exAddExp : Exp :=
  .letin (.iconst 3)
    (.letin (.iconst 4)
      (.add (.bvar 1) (.bvar 0)))
def exAddTy : Ty := IntN 7

example (κ : KEnv) : topVC κ [] exAddExp exAddTy := by
  simp [topVC, exAddExp, exAddTy]

/-! ## Declarative-side examples (via `topVC_decl_sound`) -/

-- Identity (λx. x) is declaratively typeable at Pos → Pos.
example (κ : KEnv) : Hastype κ [] ex2Exp ex2Ty := by
  apply topVC_decl_sound
  simp [topVC, ex2Exp, exId, ex2Ty, Pos]
  intros; assumption

-- let z = 5 in z is declaratively typeable at Pos.
example (κ : KEnv) : Hastype κ [] ex3Exp ex3Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, sub, implyBind, ex3Exp, ex3Ty, Pos, prim, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar]

/-! ## Declarative-side: direct constructor derivations -/

example (κ : KEnv) : Hastype κ [] (.iconst 5) (prim 5) := .int_const

example (κ : KEnv) : Hastype κ [] (.bconst true) (primBool true) := .bool_const

example (κ : KEnv) (x : EVar) (t : Ty) (Γ : TEnv) (h : Γ.lookup x = some t) :
    Hastype κ Γ (.fvar x) (self x t) :=
  .var h

example (κ : KEnv) : Hastype κ [] (.ann (.iconst 5) (prim 5)) (prim 5) :=
  .ann .int_const

example (κ : KEnv) (Γ : TEnv) (x y : EVar) (r₁ r₂ : Refinement .int)
    (hx : Γ.lookup x = some (.refine .int r₁))
    (hy : Γ.lookup y = some (.refine .int r₂)) :
    Hastype κ Γ (.add (.fvar x) (.fvar y))
      (.refine .int ⟨.eqI (.fvar .int nuName)
                          (.add (.fvar .int x) (.fvar .int y))⟩) :=
  .add_var hx hy
