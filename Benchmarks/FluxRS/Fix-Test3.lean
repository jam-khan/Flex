import LeanFixpoint

/-!
  Reproducer: PA produces an UNSOUND-shaped solution containing
  `z0 ≤ 0`. Combined with `z0 ≥ 0` this forces `z0 = 0`, which makes
  the residual goal unprovable.

  Constraint shape: classic counter loop
    init:      k0 0 n₀ n₀                          (res = 0, i = n, n)
    exit:      k0 res₀ i₀ n₀ → ¬(i₀ > 0) → res₀ = n₀
    inductive: k0 res₀ i₀ n₀ → i₀ > 0 → k0 (res₀+1) (i₀-1) n₀

  Loop invariant (true): `res₀ + i₀ = n₀ ∧ res₀ ≥ 0 ∧ i₀ ≥ 0 ∧ res₀ ≤ n₀`.

  Liquid-fixpoint produces:
    k0(z0, z1, z2) = (z0 + z1 = z2) ∧ z0 ≥ 0 ∧ z1 ≥ 0 ∧ z0 ≤ z2

  Our `solve_fixpoint` PA pass produces a much bigger conjunction that
  includes the candidate `z0 ≤ 0` (which should have been eliminated by
  the inductive clause: `res₀ ≤ 0 ∧ i₀ > 0 ⊬ (res₀+1) ≤ 0`).

  Expectation: this file currently FAILS — the residual proof can't be
  closed because `z0 = 0` is forced. Goal: PA should drop `z0 ≤ 0` (and
  `z0 = 0`, etc.) during weakening.
-/

@[qualif]
def FT3.Auto_240_244 (a'₂ : Int) (a'₃ : Int) (a'₄ : Int) : Prop :=
  ((((a'₂ + a'₃) = a'₄) ∧ (a'₃ ≥ (99 - 99))) ∧ (a'₂ ≥ (66 - 66)))

@[qualif] def FT3.EqTrue   (p : Prop) : Prop := p
@[qualif] def FT3.EqFalse  (p : Prop) : Prop := ¬p
@[qualif] def FT3.EqZero   (v : Int)  : Prop := v = 0
@[qualif] def FT3.GtZero   (v : Int)  : Prop := v > 0
@[qualif] def FT3.GeZero   (v : Int)  : Prop := v ≥ 0
@[qualif] def FT3.LtZero   (v : Int)  : Prop := v < 0
@[qualif] def FT3.LeZero   (v : Int)  : Prop := v ≤ 0

@[qualif] def FT3.Eq  (a b : Int) : Prop := a = b
@[qualif] def FT3.Gt  (a b : Int) : Prop := a > b
@[qualif] def FT3.Ge  (a b : Int) : Prop := a ≥ b
@[qualif] def FT3.Lt  (a b : Int) : Prop := a < b
@[qualif] def FT3.Le  (a b : Int) : Prop := a ≤ b
@[qualif] def FT3.Le1 (a b : Int) : Prop := a ≤ (b - 1)

def CounterLoop : Prop :=
  ∃ k0 : (a0 : Int) → (a1 : Int) → (a2 : Int) → Prop,
    ∀ (n₀ : Int),
      n₀ ≥ 0 →
        k0 0 n₀ n₀ ∧
        (∀ (res₀ : Int),
          ∀ (i₀ : Int),
            k0 res₀ i₀ n₀ →
              (¬(i₀ > 0) → res₀ = n₀) ∧
              (i₀ > 0 →
                (i₀ - 1 ≥ 0) ∧
                k0 (res₀ + 1) (i₀ - 1) n₀))

theorem CounterLoop_proof : CounterLoop := by
  solve_fixpoint
