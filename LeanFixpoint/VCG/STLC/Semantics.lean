import LeanFixpoint.VCG.STLC.Substitution

open STLC

/-! # Big-Step Operational Semantics for STLC (locally nameless)

  Call-by-value big-step semantics over locally-nameless terms. Closures carry
  a single body (`Val.clos body`) with `BVar 0` for the parameter; application
  and `letin` plug arguments in via `Exp.openVal 0`. `Val` and its operations
  live in [Substitution.lean].
-/

namespace STLC

/-- Big-step evaluation `e ⇓ v` (call-by-value, LN-substitution-based). -/
inductive BigStep : Exp → Val → Prop
  | iconst {n}   : BigStep (.iconst n) (.iconst n)
  | bconst {b}   : BigStep (.bconst b) (.bconst b)
  | lam   {body} : BigStep (.lam body)  (.clos body)
  | ann   {e t v} : BigStep e v → BigStep (.ann e t) v
  | letin {e₁ e₂ v₁ v₂} :
      BigStep e₁ v₁ →
      BigStep (e₂.openVal 0 v₁) v₂ →
      BigStep (.letin e₁ e₂) v₂
  | app   {e₁ e₂ body va v} :
      BigStep e₁ (.clos body) →
      BigStep e₂ va →
      BigStep (body.openVal 0 va) v →
      BigStep (.app e₁ e₂) v
  | add   {e₁ e₂ n₁ n₂} :
      BigStep e₁ (.iconst n₁) → BigStep e₂ (.iconst n₂) →
      BigStep (.add e₁ e₂) (.iconst (n₁ + n₂))
  | leq   {e₁ e₂ n₁ n₂} :
      BigStep e₁ (.iconst n₁) → BigStep e₂ (.iconst n₂) →
      BigStep (.leq e₁ e₂) (.bconst (decide (n₁ ≤ n₂)))
  | not_  {e b} :
      BigStep e (.bconst b) →
      BigStep (.not e) (.bconst (!b))
  | and_  {e₁ e₂ b₁ b₂} :
      BigStep e₁ (.bconst b₁) → BigStep e₂ (.bconst b₂) →
      BigStep (.and e₁ e₂) (.bconst (b₁ && b₂))
  | ite_t {e₀ e₁ e₂ v} :
      BigStep e₀ (.bconst true)  → BigStep e₁ v →
      BigStep (.ite e₀ e₁ e₂) v
  | ite_f {e₀ e₁ e₂ v} :
      BigStep e₀ (.bconst false) → BigStep e₂ v →
      BigStep (.ite e₀ e₁ e₂) v

/-- Big-step is deterministic. -/
theorem BigStep.det {e : Exp} {v₁ v₂ : Val}
    (h₁ : BigStep e v₁) (h₂ : BigStep e v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | iconst => cases h₂; rfl
  | bconst => cases h₂; rfl
  | lam    => cases h₂; rfl
  | ann _ ih => cases h₂ with | ann h => exact ih h
  | letin _ _ ih₁ ih₂ =>
    cases h₂ with
    | letin h₁' h₂' =>
      have e₁ := ih₁ h₁'
      subst e₁
      exact ih₂ h₂'
  | app _ _ _ ihf iha ihb =>
    cases h₂ with
    | app hf' ha' hb' =>
      have ef := ihf hf'
      cases ef
      have ea := iha ha'
      cases ea
      exact ihb hb'
  | add _ _ ih₁ ih₂ =>
    cases h₂ with
    | add h₁' h₂' =>
      have e₁ := ih₁ h₁'; cases e₁
      have e₂ := ih₂ h₂'; cases e₂
      rfl
  | leq _ _ ih₁ ih₂ =>
    cases h₂ with
    | leq h₁' h₂' =>
      have e₁ := ih₁ h₁'; cases e₁
      have e₂ := ih₂ h₂'; cases e₂
      rfl
  | not_ _ ih =>
    cases h₂ with
    | not_ h => have e := ih h; cases e; rfl
  | and_ _ _ ih₁ ih₂ =>
    cases h₂ with
    | and_ h₁' h₂' =>
      have e₁ := ih₁ h₁'; cases e₁
      have e₂ := ih₂ h₂'; cases e₂
      rfl
  | ite_t _ _ ih₀ ih₁ =>
    cases h₂ with
    | ite_t h₀' h₁' => exact ih₁ h₁'
    | ite_f h₀' _ =>
      have e := ih₀ h₀'
      cases e
  | ite_f _ _ ih₀ ih₂ =>
    cases h₂ with
    | ite_t h₀' _ =>
      have e := ih₀ h₀'
      cases e
    | ite_f h₀' h₂' => exact ih₂ h₂'

end STLC
