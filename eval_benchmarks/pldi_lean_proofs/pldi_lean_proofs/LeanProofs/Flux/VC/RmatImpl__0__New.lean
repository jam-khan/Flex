import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RmatImpl__0__New := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (rows₀ : Int),
  ∀ (cols₀ : Int),
   ∀ (elem₀ : Int),
    (rows₀ ≥ 0) ->
     (cols₀ ≥ 0) ->
      (((k0 0 0 rows₀ cols₀ elem₀))) ∧
      (∀ (inner₀ : Int),
       ∀ (i₀ : Int),
        ((k0 inner₀ i₀ rows₀ cols₀ elem₀)) ->
         ((¬(i₀ < rows₀)) ->
          (∀ (a'₃ : Int),
           ((k1 a'₃ inner₀ i₀ rows₀ cols₀ elem₀)) ->
            (a'₃ = cols₀)) ∧
          ((inner₀ = rows₀))
          ) ∧
         ((i₀ < rows₀) ->
          (∀ (a'₄ : Int),
           ((k1 a'₄ inner₀ i₀ rows₀ cols₀ elem₀)) ->
            ((k2 a'₄ rows₀ cols₀ elem₀ inner₀ i₀))) ∧
          (((k2 cols₀ rows₀ cols₀ elem₀ inner₀ i₀))) ∧
          (((k0 (inner₀ + 1) (i₀ + 1) rows₀ cols₀ elem₀))) ∧
          (∀ (a'₅ : Int),
           ((k2 a'₅ rows₀ cols₀ elem₀ inner₀ i₀)) ->
            ((k1 a'₅ (inner₀ + 1) (i₀ + 1) rows₀ cols₀ elem₀)))
          )
         )
      
end F
