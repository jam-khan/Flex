import LeanFixpoint.VCG.While.Hoare

/-! # Verified Constraint Generation

  Decorated commands, verification condition extraction, and the
  soundness theorem connecting VCs to valid Hoare triples.

  Following Software Foundations (Hoare2), but the `while` case
  uses an existential κ (unknown loop invariant) so that the
  resulting VCs form Constrained Horn Clauses solvable by `solve_fixpoint`.
-/

/-! ## Decorated Commands

  A decorated command carries postconditions at each point.
  The precondition is supplied externally (by context or by `decorated`).

  Key design: `DCWhile` takes a loop invariant `Inv` as annotation.
  When we don't know the invariant, we existentially quantify over it
  in `verification_conditions_from`, producing `∃ Inv, ...`.
-/

inductive DCom : Type where
  | skip   (Q : Assertion)
  | seq    (d₁ d₂ : DCom)
  | assign (x : CVar) (a : AExpr) (Q : Assertion)
  | ite    (b : BExpr) (P₁ : Assertion) (d₁ : DCom)
           (P₂ : Assertion) (d₂ : DCom) (Q : Assertion)
  | cwhile (b : BExpr) (P : Assertion) (d : DCom) (Q : Assertion)
           -- d.postQ is the loop invariant; P is the precondition for the body
  | pre    (P : Assertion) (d : DCom)
  | post   (d : DCom) (Q : Assertion)

/-- A full decorated program: precondition + decorated command. -/
structure Decorated where
  pre : Assertion
  body : DCom

/-! ## Erasure: decorated command → plain command -/

def DCom.erase : DCom → Cmd
  | .skip _           => .skip
  | .seq d₁ d₂        => .seq d₁.erase d₂.erase
  | .assign x a _     => .assign x a
  | .ite b _ d₁ _ d₂ _ => .ite b d₁.erase d₂.erase
  | .cwhile b _ d _   => .cwhile b d.erase
  | .pre _ d          => d.erase
  | .post d _         => d.erase

def Decorated.eraseCmd (dec : Decorated) : Cmd := dec.body.erase

/-! ## Postcondition extraction -/

def DCom.postQ : DCom → Assertion
  | .skip Q           => Q
  | .seq _ d₂         => d₂.postQ
  | .assign _ _ Q     => Q
  | .ite _ _ _ _ _ Q  => Q
  | .cwhile _ _ _ Q   => Q
  | .pre _ d          => d.postQ
  | .post _ Q         => Q

/-! ## Assertion implication (notation) -/

def assertImplies (P Q : Assertion) : Prop := ∀ s, P s → Q s

infixr:60 " ->> " => assertImplies

/-! ## Verification Condition Extraction

  `vcond P d` extracts the verification conditions for decorated command `d`
  under precondition `P`. The result is a `Prop` — if provable, then
  `ValidHoareTriple P d.erase d.postQ` holds.
-/

def vcond (P : Assertion) : DCom → Prop
  | .skip Q =>
    P ->> Q

  | .seq d₁ d₂ =>
    vcond P d₁ ∧ vcond d₁.postQ d₂

  | .assign x a Q =>
    P ->> (fun s => Q (s[x ↦ a.eval s]))

  | .ite b P₁ d₁ P₂ d₂ Q =>
      ((fun s => P s ∧ b.eval s = true) ->> P₁)
    ∧ ((fun s => P s ∧ b.eval s = false) ->> P₂)
    ∧ (d₁.postQ ->> Q)
    ∧ (d₂.postQ ->> Q)
    ∧ vcond P₁ d₁
    ∧ vcond P₂ d₂

  | .cwhile b Pbody d Q =>
    -- d.postQ is the loop invariant (SF convention)
      (P ->> d.postQ)
    ∧ ((fun s => d.postQ s ∧ b.eval s = true) ->> Pbody)
    ∧ vcond Pbody d
    ∧ ((fun s => d.postQ s ∧ b.eval s = false) ->> Q)

  | .pre P' d =>
    (P ->> P') ∧ vcond P' d

  | .post d Q =>
    vcond P d ∧ (d.postQ ->> Q)

/-! ## Verification conditions for a full decorated program -/

def Decorated.vconds (dec : Decorated) : Prop :=
  vcond dec.pre dec.body

/-! ## The outer triple -/

def Decorated.outerTriple (dec : Decorated) : Prop :=
  ValidHoareTriple dec.pre dec.eraseCmd dec.body.postQ

/-! ## Soundness: verification conditions imply the Hoare triple -/

theorem vcond_sound (P : Assertion) (d : DCom) :
    vcond P d → ValidHoareTriple P d.erase d.postQ := by
  induction d generalizing P with
  | skip Q =>
    intro h
    exact hoare_consequence_pre hoare_skip h
  | assign x a Q =>
    intro h
    exact hoare_consequence_pre hoare_assign h
  | seq d₁ d₂ ih₁ ih₂ =>
    intro ⟨h₁, h₂⟩
    exact hoare_seq (ih₁ P h₁) (ih₂ _ h₂)
  | ite b P₁ d₁ P₂ d₂ Q ih₁ ih₂ =>
    intro ⟨ht, hf, hpost₁, hpost₂, hvc₁, hvc₂⟩
    apply hoare_if
    · exact hoare_consequence_pre
        (hoare_consequence_post (ih₁ P₁ hvc₁) hpost₁) ht
    · exact hoare_consequence_pre
        (hoare_consequence_post (ih₂ P₂ hvc₂) hpost₂) hf
  | cwhile b Pbody d Q ih =>
    intro ⟨hinit, hbody_pre, hvc, hpost⟩
    apply hoare_while hinit _ hpost
    exact hoare_consequence_pre (ih Pbody hvc) hbody_pre
  | pre P' d ih =>
    intro ⟨himp, hvc⟩
    exact hoare_consequence_pre (ih P' hvc) himp
  | post d Q ih =>
    intro ⟨hvc, himp⟩
    exact hoare_consequence_post (ih P hvc) himp

theorem verification_correct (dec : Decorated) :
    dec.vconds → dec.outerTriple := by
  exact vcond_sound dec.pre dec.body
