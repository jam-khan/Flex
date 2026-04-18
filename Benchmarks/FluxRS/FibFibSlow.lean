import Lean
import LeanFixpoint

open Lean Meta

@[grind]
def fib_spec_fib (n : Int) : Int :=
  if n <= 1 then 1
  else fib_spec_fib (n - 1) + fib_spec_fib (n - 2)
  termination_by n.toNat

@[qualif] def q_le          (a b : Int) : Prop := a ≤ b
@[qualif] def q_gt_one      (v : Int)   : Prop := v > 1
@[qualif] def q_eq_fib      (v i : Int) : Prop := v = fib_spec_fib i
@[qualif] def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec_fib (i - 1)

def FibFibSlow :=
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((¬(n₀ ≤ 1)) ->
    (((n₀ - 1) ≥ 0)) ∧
    (((fib_spec_fib (n₀ - 1)) ≥ 0) ->
     (((n₀ - 2) ≥ 0)) ∧
     (((fib_spec_fib (n₀ - 2)) ≥ 0) ->
      (((fib_spec_fib (n₀ - 1)) + (fib_spec_fib (n₀ - 2))) = (fib_spec_fib n₀)))
     )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_spec_fib n₀)))

def FibFibSlow_proof : FibFibSlow := by
  -- solve_fixpoint
  sorry

#eval show MetaM Unit from do
  let qs ← getQualifiers
  for q in qs do
    let ty ← inferType q
    let ci ← getConstInfo q.constName!
    IO.println s!" {q} : {← ppExpr ty}"
    if let some val := ci.value? then
      IO.println s!"    = {← ppExpr val}"

example (i n : Int)   :
    (i + 1) ≤ n → fib_spec_fib i = fib_spec_fib ((i + 1) - 1) := by
  grind
