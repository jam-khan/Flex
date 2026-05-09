import LeanFixpoint

/-!
  Reproducer: pure arithmetic goal, no κ-vars.

  `aesop` fails ("failed to prove the goal after exhaustive search") on this
  shape, but plain `grind` closes it. `solve_fixpoint`'s `tryClosers` ladder
  tries `native_decide → grind → aesop → omega → bv_decide → constructor+grind`,
  with `grind` ahead of `aesop`, so the tactic should one-shot it.
-/

def NoKappaArith : Prop :=
  ∀ (v₀ : Int),
    v₀ ≥ 0 →
      v₀ < 10 →
        ∀ (v₁ : Int),
          v₁ ≥ 0 →
            v₁ < 10 →
              ∀ (v₂ : Int),
                v₂ ≥ 0 →
                  v₂ < 10 →
                    (v₀ + v₁) + v₂ < 30

theorem NoKappaArith_proof : NoKappaArith := by
  solve_fixpoint
