import Lean

import LeanFixpoint.Tactic.SolveFixpoint
import LeanFixpoint.Tactic.Command

import Lean
open Lean Meta Elab Term Tactic

def kappaWitness (x z : Int) : Prop :=
  ∃ ν : Int, ν = x - 1 ∧ z = ν

def ex1Constraint : Prop :=
  ∃ kappa : Int → Int → Prop,
    ∀ x : Int,
      (0 ≤ x) →
        (∀ ν : Int, ν == x - 1 → (kappa ν x))
      ∧ (∀ y : Int, (kappa y x) →
          ∀ ν : Int, ν == y + 1 → 0 ≤ ν )

theorem ex1Constraint_holds : ex1Constraint := by
  refine ⟨fun z x => ∃ x, 0 ≤ x ∧ kappaWitness x z, ?_⟩
  intro x hx
  unfold kappaWitness
  constructor
  · intro ν hν
    grind
  · intro y ⟨x', hx', ν', hν', hy⟩ ν hν
    grind

set_option pp.all true in
-- #check (ex1Constraint)

-- Even better — see it as a term tree
-- #print ex1Constraint

elab "#show_expr" t:term : command => do
  let e ← Lean.Elab.Command.liftTermElabM do
    let e ← Lean.Elab.Term.elabTerm t none
    let e ← Lean.Meta.reduceAll e
    return e
  logInfo m!"Expr: {repr e}"

-- #show_expr (∃ kappa : Int → Prop, ∀ x : Int, (0 ≤ x) → True)
