import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def HeapsortShiftDown := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (len₀ : Int),
  ∀ (s₀ : Int),
   ∀ (e₀ : Int),
    (s₀ < len₀) ->
     (e₀ < len₀) ->
      (s₀ ≥ 0) ->
       (e₀ ≥ 0) ->
        (((k0 s₀ len₀ s₀ e₀))) ∧
        (∀ (root₀ : Int),
         ((k0 root₀ len₀ s₀ e₀)) ->
          (¬(((root₀ * 2) + 1) > e₀)) ->
           ((¬((((root₀ * 2) + 1) + 1) ≤ e₀)) ->
            ((k1 len₀ s₀ e₀ root₀))) ∧
           (((((root₀ * 2) + 1) + 1) ≤ e₀) ->
            ((((root₀ * 2) + 1) < len₀)) ∧
            (∀ (a'₁ : Int),
             (((((root₀ * 2) + 1) + 1) < len₀)) ∧
             (∀ (a'₂ : Int),
              ((¬(a'₁ < a'₂)) ->
               ((k1 len₀ s₀ e₀ root₀))) ∧
              ((a'₁ < a'₂) ->
               ((k2 (((root₀ * 2) + 1) + 1) len₀ s₀ e₀ root₀)))
              )
             )
            ) ∧
           (((k1 len₀ s₀ e₀ root₀)) ->
            ((k2 ((root₀ * 2) + 1) len₀ s₀ e₀ root₀))) ∧
           (∀ (child₀ : Int),
            ((k2 child₀ len₀ s₀ e₀ root₀)) ->
             ((root₀ < len₀)) ∧
             (∀ (a'₄ : Int),
              ((child₀ < len₀)) ∧
              (∀ (a'₅ : Int),
               (a'₄ < a'₅) ->
                ((root₀ < len₀)) ∧
                ((child₀ < len₀)) ∧
                (((k0 child₀ len₀ s₀ e₀)))
                )
              )
             )
           )
        
end F
