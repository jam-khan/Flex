import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KmeansKmeansStep := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   ∀ (ps₀ : Int),
    (0 < k₀) ->
     (n₀ ≥ 0) ->
      (k₀ ≥ 0) ->
       (((k0 0 n₀ k₀ ps₀))) ∧
       (∀ (a'₁ : Int),
        (a'₁ = n₀) ->
         ((k1 a'₁ 0 n₀ k₀ ps₀))) ∧
       (∀ (i₀ : Int),
        ((k0 i₀ n₀ k₀ ps₀)) ->
         (ps₀ ≥ 0) ->
          ((¬(i₀ < ps₀)) ->
           ∀ (a'₃ : Int),
            ((k1 a'₃ i₀ n₀ k₀ ps₀)) ->
             (a'₃ = n₀)) ∧
          ((i₀ < ps₀) ->
           (∀ (a'₄ : Int),
            (a'₄ = n₀) ->
             ((k2 a'₄ n₀ k₀ ps₀ i₀))) ∧
           (∀ (p₀ : Int),
            ((k2 p₀ n₀ k₀ ps₀ i₀)) ->
             (∀ (a'₆ : Int),
              (a'₆ = n₀) ->
               (a'₆ = p₀)) ∧
             (∀ (j₀ : Int),
              (j₀ < k₀) ->
               (j₀ ≥ 0) ->
                (∀ (a'₈ : Int),
                 ((k1 a'₈ i₀ n₀ k₀ ps₀)) ->
                  ((k3 a'₈ n₀ k₀ ps₀ i₀ p₀ j₀))) ∧
                (∀ (a'₉ : Int),
                 ((k3 a'₉ n₀ k₀ ps₀ i₀ p₀ j₀)) ->
                  ((p₀ = a'₉)) ∧
                  (∀ (a'₁₀ : Int),
                   (a'₁₀ ≥ 0) ->
                    (((k0 (i₀ + 1) n₀ k₀ ps₀))) ∧
                    (∀ (a'₁₁ : Int),
                     ((k3 a'₁₁ n₀ k₀ ps₀ i₀ p₀ j₀)) ->
                      ((k1 a'₁₁ (i₀ + 1) n₀ k₀ ps₀)))
                    )
                  )
                )
             )
           )
          )
       
end F
