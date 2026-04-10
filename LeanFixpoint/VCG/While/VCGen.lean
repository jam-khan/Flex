import LeanFixpoint.VCG.While.Hoare

/-! # Verified Constraint Generation -/

inductive DCom : Type where
  | skip   (Q : Assertion)
  | seq    (d₁ d₂ : DCom)
  | assign (x : CVar) (f : State → Int) (Q : Assertion)
  | ite    (g : State → Bool) (P₁ : Assertion) (d₁ : DCom)
           (P₂ : Assertion) (d₂ : DCom) (Q : Assertion)
  | cwhile (g : State → Bool) (P : Assertion) (d : DCom) (Q : Assertion)
  | pre    (P : Assertion) (d : DCom)
  | post   (d : DCom) (Q : Assertion)

structure Decorated where
  pre : Assertion
  body : DCom

def DCom.erase : DCom → Cmd
  | .skip _             => .skip
  | .seq d₁ d₂          => .seq d₁.erase d₂.erase
  | .assign x f _       => .assign x f
  | .ite g _ d₁ _ d₂ _  => .ite g d₁.erase d₂.erase
  | .cwhile g _ d _     => .cwhile g d.erase
  | .pre _ d            => d.erase
  | .post d _           => d.erase

def Decorated.eraseCmd (dec : Decorated) : Cmd := dec.body.erase

def DCom.postQ : DCom → Assertion
  | .skip Q             => Q
  | .seq _ d₂           => d₂.postQ
  | .assign _ _ Q       => Q
  | .ite _ _ _ _ _ Q    => Q
  | .cwhile _ _ _ Q     => Q
  | .pre _ d            => d.postQ
  | .post _ Q           => Q

def assertImplies (P Q : Assertion) : Prop := ∀ s, P s → Q s
infixr:60 " ->> " => assertImplies

def vcond (P : Assertion) : DCom → Prop
  | .skip Q =>
    P ->> Q
  | .seq d₁ d₂ =>
    vcond P d₁ ∧ vcond d₁.postQ d₂
  | .assign x f Q =>
    P ->> (fun s => Q (s[x ↦ f s]))
  | .ite g P₁ d₁ P₂ d₂ Q =>
      ((fun s => P s ∧ g s = true) ->> P₁)
    ∧ ((fun s => P s ∧ g s = false) ->> P₂)
    ∧ (d₁.postQ ->> Q)
    ∧ (d₂.postQ ->> Q)
    ∧ vcond P₁ d₁
    ∧ vcond P₂ d₂
  | .cwhile g Pbody d Q =>
      (P ->> d.postQ)
    ∧ ((fun s => d.postQ s ∧ g s = true) ->> Pbody)
    ∧ vcond Pbody d
    ∧ ((fun s => d.postQ s ∧ g s = false) ->> Q)
  | .pre P' d =>
    (P ->> P') ∧ vcond P' d
  | .post d Q =>
    vcond P d ∧ (d.postQ ->> Q)

def Decorated.vconds (dec : Decorated) : Prop :=
  vcond dec.pre dec.body

def Decorated.outerTriple (dec : Decorated) : Prop :=
  ValidHoareTriple dec.pre dec.eraseCmd dec.body.postQ

theorem vcond_sound (P : Assertion) (d : DCom) :
    vcond P d → ValidHoareTriple P d.erase d.postQ := by
  induction d generalizing P with
  | skip Q =>
    intro h; exact hoare_consequence_pre hoare_skip h
  | assign x f Q =>
    intro h; exact hoare_consequence_pre hoare_assign h
  | seq d₁ d₂ ih₁ ih₂ =>
    intro ⟨h₁, h₂⟩; exact hoare_seq (ih₁ P h₁) (ih₂ _ h₂)
  | ite g P₁ d₁ P₂ d₂ Q ih₁ ih₂ =>
    intro ⟨ht, hf, hpost₁, hpost₂, hvc₁, hvc₂⟩
    apply hoare_if
    · exact hoare_consequence_pre
        (hoare_consequence_post (ih₁ P₁ hvc₁) hpost₁) ht
    · exact hoare_consequence_pre
        (hoare_consequence_post (ih₂ P₂ hvc₂) hpost₂) hf
  | cwhile g Pbody d Q ih =>
    intro ⟨hinit, hbody_pre, hvc, hpost⟩
    apply hoare_while hinit _ hpost
    exact hoare_consequence_pre (ih Pbody hvc) hbody_pre
  | pre P' d ih =>
    intro ⟨himp, hvc⟩; exact hoare_consequence_pre (ih P' hvc) himp
  | post d Q ih =>
    intro ⟨hvc, himp⟩; exact hoare_consequence_post (ih P hvc) himp

theorem verification_correct (dec : Decorated) :
    dec.vconds → dec.outerTriple :=
  vcond_sound dec.pre dec.body
