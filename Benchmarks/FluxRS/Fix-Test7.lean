import LeanFixpoint

/-!
  Reproducer: Append — `solve_fixpoint`'s κ-solutions differ from those
  produced by `fixpoint-hs`.

  fixpoint-hs solutions (paper-faithful):
    k0(z0,z1,z2) =
      (∃a0. z0 = a0+n2+1 ∧ n1 = a0+1 ∧ a0 ≥ 0 ∧ a0+n2 ≥ 0
            ∧ z1 = n1 ∧ z2 = n2 ∧ n1 ≥ 0 ∧ n2 ≥ 0)
      ∨ (z0 = n2 ∧ z1 = n1 ∧ z2 = n2 ∧ n1 = 0 ∧ n1 ≥ 0 ∧ n2 ≥ 0)

    k1(z0,z1,z2,z3,z4) =
      z0 = a0+n2 ∧ z1 = n1 ∧ z2 = n2 ∧ z3 = a0 ∧ z4 = a1
        ∧ n1 = a0+1 ∧ a0 ≥ 0 ∧ n1 ≥ 0 ∧ n2 ≥ 0 ∧ a0+n2 ≥ 0

  Investigation:
    - Compare our sol1 output to the above structure.
    - Likely candidates for the divergence: our `stripScopePrefix` may not
      substitute every outer binder (n1₀, n2₀, n₀, a'₁) into κ-param positions,
      leaving extra ∃-quantifiers, OR our smart-And/Or aren't reducing
      paper-equivalent shapes.
    - Note fixpoint-hs's sols still have free `n1, n2, a0, a1` that get
      captured at use sites — same paper-faithful pattern we discussed.
-/

def AppendTest := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop,
              ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop,
 ∀ (n1₀ : Int),
  ∀ (n2₀ : Int),
   (n1₀ ≥ 0) ->
    (n2₀ ≥ 0) ->
     ((n1₀ = 0) ->
      ((k0 n2₀ n1₀ n2₀))) ∧
     (∀ (n₀ : Int),
      (n1₀ = (n₀ + 1)) ->
       ∀ (a'₁ : Int),
        (n₀ ≥ 0) ->
         ((n₀ + n2₀) ≥ 0) ->
          (((k1 (n₀ + n2₀) n1₀ n2₀ n₀ a'₁))) ∧
          (∀ (a'₂ : Int),
           ((k1 a'₂ n1₀ n2₀ n₀ a'₁)) ->
            (a'₂ ≥ 0) ->
             ((k0 (a'₂ + 1) n1₀ n2₀)))
          ) ∧
     (∀ (a'₃ : Int),
      ((k0 a'₃ n1₀ n2₀)) ->
       (a'₃ = (n1₀ + n2₀)))

theorem Append_proof : AppendTest := by
  solve_fixpoint
