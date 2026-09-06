import Flex.Tactic

/-!
  # `#spec` discharge machinery

  Support tactics and lemmas for the `#spec` command (`Flex.Front.Spec`): the
  default discharge ladder `flex_spec_solve`, the foldl invariant-introduction
  lemma that routes higher-order goals into the CHC solver, and a small goal
  normalizer required between `apply` and `fix`.
-/

open Lean Elab Tactic

/-- Replace the target with `instantiateMVars` of itself.

Needed after `apply foldl_inv_spec`: `apply` assigns the postcondition
metavariable `?P` but leaves it *syntactically* in the goal, and
`pa_cert`/`walkPAProof` rejects any mvar-headed subterm ("head metavariable …
is not a cut variable"). Instantiating the target before `fix` fixes this
without touching the solver. -/
elab "instantiate_goal" : tactic => do
  let g ← getMainGoal
  let g' ← g.replaceTargetDefEq (← instantiateMVars (← g.getType))
  replaceMainGoal [g']

/-- Invariant-introduction lemma for `List.foldl`: to prove `P` of a fold,
exhibit an accumulator invariant `inv` that holds of the seed, is preserved by
each step, and implies `P`.

The hypothesis is deliberately phrased in the benchmark CHC clause style
(`∀ v, v = seed → inv v`; guard-chained step; check clause) so that `exprFlat`
splits it into exactly the flat `∀ x̄, guards → head` clauses predicate
abstraction is tuned for. `inv` is the κ: `#spec` users never write it —
`fix` infers it from the `@[qualif]` bank. -/
theorem foldl_inv_spec {α β : Type} (xs : List α) (f : β → α → β) (init : β)
    (P : β → Prop)
    (h : ∃ inv : β → Prop,
        (∀ v, v = init → inv v)
      ∧ (∀ b, inv b → ∀ a, a ∈ xs → ∀ v, v = f b a → inv v)
      ∧ (∀ b, inv b → P b)) :
    P (xs.foldl f init) := by
  obtain ⟨inv, hseed, hstep, hout⟩ := h
  exact hout _ (List.foldlRecOn xs f (hseed init rfl)
    (fun b hb a ha => hstep b hb a ha _ rfl))

/-- Default discharge ladder for `#spec f …` goals. Each rung must end in
`done`: `first` treats a rung that merely *leaves* goals as success, which
would surface as "unsolved goals" at the generated theorem.

  1. first-order bodies; also modular composition — callee specs fire through
     their `grind_pattern`s inside `leafClosers`' grind rung, callees stay
     folded.
  2. recursive definitions — the spec rides the functional-induction motive.
  3. `List.foldl` bodies — rewrite via `foldl_inv_spec`, then `fix` infers the
     accumulator invariant κ from the `@[qualif]` bank. -/
syntax "flex_spec_solve" ident : tactic

macro_rules
  | `(tactic| flex_spec_solve $f:ident) =>
    `(tactic| first
        | (intros; unfold $f:ident; leafClosers; done)
        | (intros; fun_induction $f:ident <;> leafClosers; done)
        | (intros; unfold $f:ident;
           apply foldl_inv_spec; instantiate_goal; fix; done))
