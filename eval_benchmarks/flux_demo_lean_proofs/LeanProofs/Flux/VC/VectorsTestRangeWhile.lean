import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def VectorsTestRangeWhile := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ ≥ 0) ->
    (hi₀ ≥ 0) ->
     (lo₀ ≤ hi₀) ->
      (0 ≤ (hi₀ - lo₀)) ->
       (((k0 (hi₀ - lo₀) lo₀ hi₀))) ∧
       (∀ (v₀ : Int),
        ((lo₀ ≤ v₀) ∧ (v₀ < hi₀)) ->
         ((k1 v₀ (hi₀ - lo₀) lo₀ hi₀))) ∧
       (∀ (rng₀ : Int),
        ((k0 rng₀ lo₀ hi₀)) ->
         (rng₀ ≠ 0) ->
          ((rng₀ > 0)) ∧
          (∀ (a'₄ : Int),
           ((k1 a'₄ rng₀ lo₀ hi₀)) ->
            ((k2 a'₄ lo₀ hi₀ rng₀))) ∧
          ((0 ≤ (rng₀ - 1)) ->
           ∀ (val₀ : Int),
            ((k2 val₀ lo₀ hi₀ rng₀)) ->
             (val₀ ≥ 0) ->
              (((lo₀ ≤ val₀) = True)) ∧
              (((k0 (rng₀ - 1) lo₀ hi₀))) ∧
              (∀ (a'₆ : Int),
               ((k2 a'₆ lo₀ hi₀ rng₀)) ->
                ((k1 a'₆ (rng₀ - 1) lo₀ hi₀)))
              )
          )
       
end F
