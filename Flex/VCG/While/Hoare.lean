import Flex.VCG.While.Semantics

/-! # Hoare Logic Soundness Lemmas -/

@[simp]
theorem hoare_skip {P : Assertion} :
    ValidHoareTriple P .skip P := by
  intro s₁ s₂ h hp; cases h; exact hp

@[simp]
theorem hoare_assign {Q : Assertion} {x : CVar} {f : State → Int} :
    ValidHoareTriple (fun s => Q (s[x ↦ f s])) (.assign x f) Q := by
  intro s₁ s₂ h hp; cases h; exact hp

@[simp]
theorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd} :
    ValidHoareTriple P c₁ R →
    ValidHoareTriple R c₂ Q →
    ValidHoareTriple P (.seq c₁ c₂) Q := by
  intro hc1 hc2 s₁ s₃ heval hp
  cases heval
  exact hc2 _ _ ‹_› (hc1 _ _ ‹_› hp)

@[simp]
theorem hoare_if {P Q : Assertion} {g : State → Bool} {c₁ c₂ : Cmd} :
    ValidHoareTriple (fun s => P s ∧ g s = true) c₁ Q →
    ValidHoareTriple (fun s => P s ∧ g s = false) c₂ Q →
    ValidHoareTriple P (.ite g c₁ c₂) Q := by
  intro ht hf s₁ s₂ heval hp
  cases heval
  · exact ht _ _ ‹_› ⟨hp, ‹_›⟩
  · exact hf _ _ ‹_› ⟨hp, ‹_›⟩

@[simp]
theorem while_inv
    {Inv Q : Assertion} {g : State → Bool} {c : Cmd}
    (hpres : ValidHoareTriple (fun s => Inv s ∧ g s = true) c Inv)
    (hpost : ∀ s, Inv s ∧ g s = false → Q s)
    {s₁ s₂ : State} (heval : Ceval (.cwhile g c) s₁ s₂) :
    Inv s₁ → Q s₂ := by
  generalize hcmd : Cmd.cwhile g c = cmd at heval
  induction heval with
  | while_false hb =>
    intro hi; cases hcmd; exact hpost _ ⟨hi, hb⟩
  | @while_true _ s₁' s₂' g' s₃' hb hc _ ih_body ih_while =>
    intro hi; cases hcmd; exact ih_while rfl (hpres _ _ hc ⟨hi, hb⟩)
  | _ => intro; simp_all

@[simp]
theorem hoare_while {P Q Inv : Assertion} {g : State → Bool} {c : Cmd} :
    (∀ s, P s → Inv s) →
    ValidHoareTriple (fun s => Inv s ∧ g s = true) c Inv →
    (∀ s, Inv s ∧ g s = false → Q s) →
    ValidHoareTriple P (.cwhile g c) Q := by
  intro hinit hpres hpost s₁ s₂ heval hp
  exact while_inv hpres hpost heval (hinit _ hp)

@[simp]
theorem hoare_consequence_pre {P P' Q : Assertion} {c : Cmd} :
    ValidHoareTriple P' c Q →
    (∀ s, P s → P' s) →
    ValidHoareTriple P c Q := by
  intro h himp s₁ s₂ heval hp
  exact h _ _ heval (himp _ hp)

@[simp]
theorem hoare_consequence_post {P Q Q' : Assertion} {c : Cmd} :
    ValidHoareTriple P c Q' →
    (∀ s, Q' s → Q s) →
    ValidHoareTriple P c Q := by
  intro h himp s₁ s₂ heval hp
  exact himp _ (h _ _ heval hp)
