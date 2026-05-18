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
abbrev IntR (x : EVar) (k : STLC.KVar) : Ty :=
  .refine .int ⟨.kapp k [⟨.int, .fvar .int x⟩, ⟨.int, .fvar .int nuName⟩]⟩

/-- Identity function under LN. -/
abbrev exId : Exp := .lam (.bvar 0)

/-- Function type for identity at `IntK k → IntK k`. -/
abbrev ty_k (k : STLC.KVar) : Ty := .arrow (IntK k) (IntK k)

/-- Function type for `TT → IntR x k`. -/
abbrev ty_xk (x : EVar) (k : STLC.KVar) : Ty := .arrow TT (IntR x k)

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

example :
    ∃ κ : KEnv,
      Check κ []
        (.letin (.iconst 99) (.app (.ann exId (ty_k "k")) (.bvar 0)))
        Pos := by
  make_horn_under_k [List.lookup]
  solve_fixpoint

/-! ## κ-example with `ty_xk`: same shape, output type `IntN 99` -/

example :
    ∃ κ : KEnv,
      Check κ []
        (.letin (.iconst 99) (.app (.ann exId (ty_xk "x" "k")) (.bvar 0)))
        (IntN 99) := by
  make_horn_under_k [List.lookup]
  solve_fixpoint

/-! ## Example 3 again: prove `topVC` without solver -/

example (κ : KEnv) : topVC κ [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, sub, implyBind, ex3Exp, ex3Ty, Pos, prim, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar]

/-! ## `exGt`: `λx. λy. ¬(x ≤ y) ⇐ TT → TT → {ν | ν ↔ x > y}`

  ⛔ Uses `Synth.not_` which is deferred. Skipped pending the
  existential-refinement helper. Original:

  ```
  abbrev exGt : Exp := .lam "x" (.lam "y" (.not (.leq (.var "x") (.var "y"))))
  abbrev tyGt : Ty := Ty.arrow "x" TT
    (Ty.arrow "y" TT (.refine .bool ⟨fun ρ v => v = (ρ.ints "x" > ρ.ints "y")⟩))

  example : topVC [] exGt tyGt := by
    simp [topVC, check, synth, List.lookup]
  ```
-/

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
  make_horn_under_k [List.lookup]
  solve_fixpoint

/-! ## Arithmetic: `let a = 3 in let b = 4 in a + b ⇐ IntN 7` -/

def exAddExp : Exp :=
  .letin (.iconst 3)
    (.letin (.iconst 4)
      (.add (.bvar 1) (.bvar 0)))
def exAddTy : Ty := IntN 7

example (κ : KEnv) : topVC κ [] exAddExp exAddTy := by
  simp [topVC, check, synth, implyBind, exAddExp, exAddTy, IntN, prim, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar, List.lookup]

/-! ## Declarative-side examples (via `topVC_decl_sound`) -/

-- Identity (λx. x) is declaratively typeable at Pos → Pos.
example (κ : KEnv) : Hastype κ [] ex2Exp ex2Ty := by
  apply topVC_decl_sound
  simp [topVC, check, synth, implyBind, ex2Exp, exId, ex2Ty, Pos, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar,
        Term.openBVar]
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
