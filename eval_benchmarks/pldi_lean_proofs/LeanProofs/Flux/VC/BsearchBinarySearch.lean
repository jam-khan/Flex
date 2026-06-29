import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BsearchBinarySearch := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (k₀ : Int),
  ∀ (items₀ : Int),
   (items₀ ≥ 0) ->
    (¬(items₀ ≤ 0)) ->
     (((items₀ - 1) ≥ 0)) ∧
     (((k0 0 (items₀ - 1) k₀ items₀))) ∧
     (∀ (low₀ : Int),
      ∀ (high₀ : Int),
       ((k0 low₀ high₀ k₀ items₀)) ->
        (low₀ ≤ high₀) ->
         (((high₀ - low₀) ≥ 0)) ∧
         ((((low₀ + ((high₀ - low₀) / 2)) < items₀)) ∧
         (∀ (a'₄ : Int),
          (a'₄ ≠ k₀) ->
           ((¬(a'₄ > k₀)) ->
            ((k1 high₀ k₀ items₀ low₀ high₀ a'₄))) ∧
           ((a'₄ > k₀) ->
            ((low₀ + ((high₀ - low₀) / 2)) ≠ 0) ->
             ((((low₀ + ((high₀ - low₀) / 2)) - 1) ≥ 0)) ∧
             (((k1 ((low₀ + ((high₀ - low₀) / 2)) - 1) k₀ items₀ low₀ high₀ a'₄)))
             ) ∧
           (∀ (high₁ : Int),
            ((k1 high₁ k₀ items₀ low₀ high₀ a'₄)) ->
             ((¬(a'₄ < k₀)) ->
              ((k2 low₀ k₀ items₀ low₀ high₀ a'₄ high₁))) ∧
             ((a'₄ < k₀) ->
              ((k2 ((low₀ + ((high₀ - low₀) / 2)) + 1) k₀ items₀ low₀ high₀ a'₄ high₁))) ∧
             (∀ (low₁ : Int),
              ((k2 low₁ k₀ items₀ low₀ high₀ a'₄ high₁)) ->
               ((k0 low₁ high₁ k₀ items₀)))
             )
           )
         )
         )
     
end F
