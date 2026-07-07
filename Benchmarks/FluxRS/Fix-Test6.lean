import Flex

/-!
  Reproducer: MinIndex — originally `solve_fixpoint` identified ALL of k0..k3
  as cyclic while `fixpoint-hs` classified only k0 (and k1) as cyclic.

  Root cause: `exprPartitionKVars` called `exprIsCyclic κ e` per-κ, flagging
  every member of a cycle's transitive closure as cyclic. Fixed by routing
  through `classifyKVars`, which runs Tarjan's SCC + the C-J §5.5 cut-set
  computation: pick a minimal vertex set whose removal makes the graph
  acyclic; cut-set members are cyclic, the rest are acyclic in the reduced
  graph.

  After the fix: `Cyclic κ: [k0]`, `Acyclic κ: [k1, k2, k3]` — even tighter
  than fixpoint-hs's report ({k0, k1}). k1/k2/k3 get fused away; k0 goes to
  PA, which needs a `z0 < z2` qualifier (res < n) to give a non-trivial sol.
-/

@[qualif] def MinIdx.q_lt      (a b : Int) : Prop := a < b
@[qualif] def MinIdx.q_le      (a b : Int) : Prop := a ≤ b
@[qualif] def MinIdx.q_ge_zero (a : Int)   : Prop := a ≥ 0
@[qualif] def MinIdx.q_eq_zero (a : Int)   : Prop := a = 0

def MinIndex := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop,
                ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop,
                ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop,
                ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop,
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (0 ≤ n₀) ->
    (n₀ ≥ 0) ->
     (((k0 0 0 n₀))) ∧
     (∀ (res₀ : Int),
      ∀ (i₀ : Int),
       ((k0 res₀ i₀ n₀)) ->
        ((¬(i₀ < n₀)) ->
         (res₀ < n₀)) ∧
        ((i₀ < n₀) ->
         (∀ (a'₂ : Int),
          ((k1 a'₂ n₀ res₀ i₀))) ∧
         (∀ (a'₃ : Int),
          ((k1 a'₃ n₀ res₀ i₀)) ->
           ((res₀ < n₀)) ∧
           (∀ (a'₄ : Int),
            ((k2 a'₄ n₀ res₀ i₀ a'₃))) ∧
           (∀ (a'₅ : Int),
            ((k2 a'₅ n₀ res₀ i₀ a'₃)) ->
             ((¬(a'₃ < a'₅)) ->
              ((k3 res₀ n₀ res₀ i₀ a'₃ a'₅))) ∧
             ((a'₃ < a'₅) ->
              ((k3 i₀ n₀ res₀ i₀ a'₃ a'₅))) ∧
             (∀ (a'₆ : Int),
              ((k3 a'₆ n₀ res₀ i₀ a'₃ a'₅)) ->
               ((k0 a'₆ (i₀ + 1) n₀)))
             )
           )
         )
        )

theorem MinIndex_proof : MinIndex := by
  solve_fixpoint
