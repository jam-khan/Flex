import LeanFixpoint.VCG.STLC.VCGen
import LeanFixpoint.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness (skeleton, κ-indexed)

  Algorithmic VC generation is sound w.r.t. the bidirectional and declarative
  typing rules. Every judgement is now parameterized by `κ : KEnv`.

  The headline theorems are stated and `sorry`-stubbed pending the full case
  analysis (deferred to Stage 13). The shape of the API is what
  `MakeHornUnderK.lean` consumes.
-/

/-! ## Sub soundness -/

theorem sub_sound (κ : KEnv) (Γ : TEnv) (s t : Ty) (c : Constraint) :
    sub s t = some c → Entail κ Γ (c κ) → Subtyp κ Γ s t := by
  sorry

/-! ## Synth / Check soundness (mutual) -/

mutual
  theorem synth_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
      synth Γ e = some (c, t) → Entail κ Γ (c κ) → Synth κ Γ e t := by
    sorry

  theorem check_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint) :
      check Γ e t = some c → Entail κ Γ (c κ) → Check κ Γ e t := by
    sorry
end

/-! ## Bidirectional → declarative -/

mutual
  theorem synth_to_hastype {κ Γ e t} : Synth κ Γ e t → Hastype κ Γ e t := by
    intro h
    match h with
    | .var hl         => exact .var hl
    | .int_const      => exact .int_const
    | .bool_const     => exact .bool_const
    | .ann hck        => exact .ann (check_to_hastype hck)
    | .app hsy hck    => exact .app (synth_to_hastype hsy) (check_to_hastype hck)
    | .add_var hx hy  => exact .add_var hx hy
    | .leq_var hx hy  => exact .leq_var hx hy

  theorem check_to_hastype {κ Γ e t} : Check κ Γ e t → Hastype κ Γ e t := by
    intro h
    match h with
    | .sub hsy hsub        => exact .sub (synth_to_hastype hsy) hsub
    | .lam L hck           => exact .lam L (fun x hx => check_to_hastype (hck x hx))
    | .letin L hsy hck     =>
        exact .letin L (synth_to_hastype hsy) (fun x hx => check_to_hastype (hck x hx))
    | .ite hlk hck1 hck2   =>
        exact .ite hlk (check_to_hastype hck1) (check_to_hastype hck2)
end

theorem synth_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Constraint) (t : Ty) :
    synth Γ e = some (c, t) → Entail κ Γ (c κ) → Hastype κ Γ e t :=
  fun h hc => synth_to_hastype (synth_sound κ Γ e c t h hc)

theorem check_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Constraint) :
    check Γ e t = some c → Entail κ Γ (c κ) → Hastype κ Γ e t :=
  fun h hc => check_to_hastype (check_sound κ Γ e t c h hc)

theorem topVC_decl_sound (κ : KEnv) (e : Exp) (t : Ty) :
    topVC κ [] e t → Hastype κ [] e t := by
  unfold topVC
  cases hck : check [] e t with
  | none   => intro hf; exact hf.elim
  | some c => intro h; exact check_decl_sound κ [] e t c hck (Entail.emp h)
