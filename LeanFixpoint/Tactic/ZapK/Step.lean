import Lean
import LeanFixpoint.Core.Types

open Lean Meta Elab Tactic Term

/-- Step in the constraint-tree descent. Each goal-side construct corresponds
    to one CHC construct, one fragment of `sol1`, and one proof tactic.

      goal-side (Lean)         CHC (paper)     sol1 fragment    step      proof tactic
      ────────────────────────────────────────────────────────────────────────────────────
      Π x:τ. _   (τ : Type)    ∀ x:b. _        ∃ x:b. _         exV x     refine ⟨x, ?_⟩
      Π _:p. _   (p : Prop)    p ⇒ _           p ∧ _            conjH h   refine ⟨h, ?_⟩
      _ ∧ _      (took L)      c₁ ∧ c₂         _ ∨ _            inL       apply Or.inl
      _ ∧ _      (took R)      c₁ ∧ c₂         _ ∨ _            inR       apply Or.inr
      κ(ȳ)                     κ(ȳ)            ⋀ᵢ zᵢ = yᵢ       —         (refl after β)

    The duality is total: every row pairs *one* goal-construct with *one*
    sol-construct. This relies on `sol` being unsimplified — see `solveHead`.
-/
inductive Step where
  | exV   (x : Expr)
  | conjH (h : Expr)
  | inL
  | inR
  deriving Inhabited

abbrev Path := List Step

-- Convert an fvar to a syntax `Ident` so it can be spliced into a tactic
-- NOT SURE ABT BELOW
private def fvarToSyntax (e : Expr) : TacticM Ident := do
  let .fvar fid := e | throwError m!"fvarToSyntax: expected fvar, got {e}"
  let lctx ← getLCtx
  let some decl := lctx.find? fid
    | throwError m!"fvarToSyntax: fvar {fid.name} not in current lctx"
  return mkIdent decl.userName


def doStep : Step → TacticM Unit
  | .exV  x => do
      let s ← fvarToSyntax x
      evalTactic (← `(tactic| refine ⟨$s:ident, ?_⟩))
  | .conjH h => do
      let s← fvarToSyntax h
      evalTactic (← `(tactic| refine ⟨$s:ident, ?_⟩))
  | .inL     => do
      evalTactic (← `(tactic| apply Or.inl))
  | .inR     => do
      evalTactic (← `(tactic| apply Or.inr))

/-- Test driver: looks up `a` and `ha` from the local context, builds an
    artificial path covering all four `Step` constructors, and runs `doStep`
    on each. -/
elab "testDoStep" : tactic => do
  let lctx ← getLCtx
  let some aDecl  := lctx.findFromUserName? `a
    | throwError "testDoStep: expected fvar `a` in scope"
  let some haDecl := lctx.findFromUserName? `ha
    | throwError "testDoStep: expected fvar `ha` in scope"
  let path : Path := [
    .exV   (.fvar aDecl.fvarId),     -- provide `a` as ∃-witness
    .inL,                             -- take left of outer ∨
    .inR,                             -- take right of inner ∨
    .conjH (.fvar haDecl.fvarId)      -- discharge `a = 1` with `ha`
  ]
  for step in path do
    doStep step

/-- One artificial test that exercises all four `Step` cases in sequence.

    Goal trace step-by-step:

    | after step    | residual goal                                     |
    |---------------|---------------------------------------------------|
    | (start)       | ∃ x : Int, (False ∨ (x = 1 ∧ True)) ∨ False       |
    | `exV a`       | (False ∨ (a = 1 ∧ True)) ∨ False                  |
    | `inL`         | False ∨ (a = 1 ∧ True)                            |
    | `inR`         | a = 1 ∧ True                                      |
    | `conjH ha`    | True                                              |

    `trivial` closes the residual `True`. If `testDoStep` is broken, this
    test fails with a type-mismatch or unsolved-goals error pointing at
    the offending step. -/
example (a : Int) (ha : a = 1) :
    ∃ x : Int, (False ∨ (x = 1 ∧ True)) ∨ False := by
  testDoStep
  trivial
----------------------------------------------------------------------
-- Test infrastructure: inline path syntax
----------------------------------------------------------------------

declare_syntax_cat zapStep
syntax "exV "   ident : zapStep
syntax "conjH " ident : zapStep
syntax "inL"          : zapStep
syntax "inR"          : zapStep

/-- Inline-path tactic: walk a list of step descriptors, looking up
    fvars by name from the current local context. -/
syntax "runPath " "[" zapStep,* "]" : tactic

elab_rules : tactic
  | `(tactic| runPath [ $steps,* ]) => do
      let lctx ← getLCtx
      let lookup (i : TSyntax `ident) : TacticM Expr := do
        let some d := lctx.findFromUserName? i.getId
          | throwError m!"runPath: no fvar `{i.getId}` in current lctx"
        return .fvar d.fvarId
      for stepStx in steps.getElems do
        let step : Step ← match stepStx with
          | `(zapStep| exV   $i:ident) => pure (.exV   (← lookup i))
          | `(zapStep| conjH $i:ident) => pure (.conjH (← lookup i))
          | `(zapStep| inL)            => pure .inL
          | `(zapStep| inR)            => pure .inR
          | _                          => throwError "runPath: malformed step"
        doStep step

----------------------------------------------------------------------
-- Harder test 1 — long ∃-chain + chained ∧-guards
-- (mirrors sol1 output for a constraint like
--   `∀ a b c, a = 1 → b = 2 → c = 3 → κ(a+b+c)`)
----------------------------------------------------------------------

/-- Six-step path: 3 value witnesses then 3 hypothesis discharges,
    closing on the residual arithmetic equality. -/
example
    (a b c : Int)
    (ha : a = 1) (hb : b = 2) (hc : c = 3) (hsum : a + b + c = 6) :
    ∃ x y z : Int, x = 1 ∧ y = 2 ∧ z = 3 ∧ x + y + z = 6 := by
  runPath [exV a, exV b, exV c, conjH ha, conjH hb, conjH hc]
  exact hsum

----------------------------------------------------------------------
-- Harder test 2 — three-way disjunction, navigation through middle branch
-- (mirrors sol1 for `(prod₁ ∨ prod₂) ∨ prod₃` shape with one κ-arm chosen)
----------------------------------------------------------------------

/-- Path takes `inR` then `inL` to land in the middle disjunct, witnesses
    its existential, discharges its guard, leaves a non-trivial arithmetic
    leaf for `grind`. -/
example
    (a : Int) (ha : 0 ≤ a)
    (b : Int) (hb : b = a + 1) :
    ∃ x : Int,
      0 ≤ x ∧
        ( (∃ ν : Int, ν = x - 1 ∧ x + ν = 2 * x - 1)
        ∨ (∃ ν : Int, ν = x + 1 ∧ x + ν = 2 * x + 1)
        ∨ False ) := by
  runPath [exV a, conjH ha, inR, inL, exV b, conjH hb]
  grind  -- closes a + b = 2 * a + 1 using hb : b = a + 1

----------------------------------------------------------------------
-- Harder test 3 — nested ∃ inside disjuncts inside ∃ (deep mixing)
-- This is closer to the real shape sol1 produces for fusion across
-- two κs with cross-flow. Tests that path entries from different
-- depths don't interfere with each other.
----------------------------------------------------------------------

example
    (a : Int) (ha : 0 ≤ a)
    (b : Int) (hb : b = a - 1)
    (c : Int) (hc : c = b + 2) :
    ∃ x : Int,
      0 ≤ x ∧
        ( ( ∃ y : Int, y = x - 1 ∧
              ∃ z : Int, z = y + 2 ∧ z = x + 1 )
        ∨ False ) := by
  runPath [exV a, conjH ha, inL, exV b, conjH hb, exV c, conjH hc]
  grind  -- closes c = a + 1 from hb, hc

----------------------------------------------------------------------
-- Harder test 4 — many chained Prop guards (mirrors Quicksort shape)
-- Tests that the conjH chain handles the bare-implication case
-- correctly when chained 4+ deep without intervening value binders.
----------------------------------------------------------------------

example
    (n : Int) (h1 : 0 ≤ n) (h2 : n < 100) (h3 : n ≠ 42) (h4 : n + 1 < 101) :
    ∃ x : Int, 0 ≤ x ∧ x < 100 ∧ x ≠ 42 ∧ x + 1 < 101 ∧ True := by
  runPath [exV n, conjH h1, conjH h2, conjH h3, conjH h4]
  trivial

----------------------------------------------------------------------
-- Harder test 5 — left then right then left, deeply
----------------------------------------------------------------------

example
    (a : Int) (ha : a = 7) :
    ∃ x : Int,
      ( ( (∃ y : Int, y = 7 ∧ False)
        ∨ (∃ y : Int, y = 7 ∧ y = x) )    -- conjuncts swapped: y = 7 first
      ∨ False ) := by
  runPath [exV a, inL, inR, exV a, conjH ha]
  rfl

