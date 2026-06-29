import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def VecFromElemN := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (elem₀ : Int),
   (n₀ ≥ 0) ->
    (((k0 0 0 n₀ elem₀))) ∧
    (∀ (vec₀ : Int),
     ∀ (i₀ : Int),
      ((k0 vec₀ i₀ n₀ elem₀)) ->
       ((¬(i₀ < n₀)) ->
        (vec₀ = n₀)) ∧
       ((i₀ < n₀) ->
        ((k0 (vec₀ + 1) (i₀ + 1) n₀ elem₀)))
       )
    
end F
