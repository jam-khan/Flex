import LeanFixpoint.VCG.STLC.Syntax
import LeanFixpoint.VCG.STLC.Semantics

namespace STLC

/-- Interpret a term under the single environment `γ`. `fvar` resolves through
    the name map (`REnv.get`); `bvar` resolves through the de Bruijn stack
    (`REnv.getBV`) — the values of ν and the enclosing quantifier/arrow binders
    live there. Both kinds of variable go *through `γ`*; nothing is substituted
    into the syntax. -/
def Term.interp (γ : REnv) : {b : Base} → Term b → b.interp
  | _, .const _ c   => c
  | _, .bvar b k    => REnv.getBV b γ k
  | _, .fvar b x    => REnv.get b γ x
  | _, .add t₁ t₂   => Term.interp γ t₁ + Term.interp γ t₂
  | _, .not t       => !Term.interp γ t
  | _, .and t₁ t₂   => Term.interp γ t₁ && Term.interp γ t₂

/-- Interpret a (now κ-free) formula under `γ`. Each quantifier binds `BVar 0`,
    so it `push`es its witness value as the new innermost de Bruijn slot of `γ`
    and recurses — the value goes *through the environment*, never substituted
    into the syntax. No κ-assignment is needed: κ-applications live one level
    up, in `Refinement`. -/
def Formula.interp (γ : REnv) : Formula → Prop
  | .tt           => True
  | .ff           => False
  | .eq _ t₁ t₂   => Term.interp γ t₁ = Term.interp γ t₂
  | .leqI t₁ t₂   => Term.interp γ t₁ ≤ Term.interp γ t₂
  | .and φ₁ φ₂    => Formula.interp γ φ₁ ∧ Formula.interp γ φ₂
  | .or φ₁ φ₂     => Formula.interp γ φ₁ ∨ Formula.interp γ φ₂
  | .not φ        => ¬ Formula.interp γ φ
  | .imp φ₁ φ₂    => Formula.interp γ φ₁ → Formula.interp γ φ₂
  | .exI φ        => ∃ n : Int,  Formula.interp (γ.push (.iconst n)) φ
  | .exB φ        => ∃ c : Bool, Formula.interp (γ.push (.bconst c)) φ
  | .allI φ       => ∀ n : Int,  Formula.interp (γ.push (.iconst n)) φ
  | .allB φ       => ∀ c : Bool, Formula.interp (γ.push (.bconst c)) φ

/-- Interpret a refinement at value ν under κ-assignment: `push` ν as the
    innermost de Bruijn slot (ν = `BVar 0`), then either interpret the formula
    or apply κ. This is the *only* interpretation that consults the κ-assignment. -/
def Refinement.interp (κ : KEnv) {b : Base} (r : Refinement b)
    (γ : REnv) (ν : b.interp) : Prop :=
  match r with
  | .fmla φ       => Formula.interp (γ.push (Val.inj b ν)) φ
  | .kapp kn args =>
      κ kn (args.map (fun a => ⟨a.1, Term.interp (γ.push (Val.inj b ν)) a.2⟩))

/-! ## Logical relation: ⟦τ⟧ as a predicate on values, κ-indexed and parameterized by γ.

  - **Refinement bases**: `v` is `.iconst n` / `.bconst b` and the deep refinement
    holds at that value under the supplied κ-assignment.
  - **Arrow**: `v` is a locally-closed closure (`.clos body` with body `lc_at 1`),
    and *for some cofinite set* `L` of names, every fresh `x ∉ L` works as an
    opener for the codomain. The cofinite shape is the canonical LN logical
    relation form (cf. Charguéraud's POPLMark-Reloaded notes) — it gives the
    consumers of the LR (`subtyp_sound`/`hastype_fundamental`) the freedom to
    pick whichever name they need via the `TyDenote.rename` lemma.

  Termination: structural by `Ty.skel`. Both recursive positions on the arrow
  case (`s` and `t.openVar 0 x`) decrease via `Ty.skel_openVar`. -/
def TyDenote : KEnv → Ty → REnv → Val → Prop
  | κ, .refine .int  r, γ, v => ∃ n : Int,  v = .iconst n ∧ Refinement.interp κ r γ n
  | κ, .refine .bool r, γ, v => ∃ b : Bool, v = .bconst b ∧ Refinement.interp κ r γ b
  | κ, .arrow s t,      γ, v =>
      ∃ body, v = .clos body ∧
        Val.lc (.clos body) ∧ Val.closed (.clos body) ∧
        ∀ va, TyDenote κ s γ va →
          ∃ vr, BigStep (body.openVal 0 va) vr ∧
                TyDenote κ t (γ.push va) vr
termination_by _ t _ _ => t.skel
decreasing_by
  all_goals simp_wf
  · omega
  · omega

end STLC
