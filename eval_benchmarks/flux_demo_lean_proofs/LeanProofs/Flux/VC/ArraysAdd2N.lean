import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def ArraysAdd2N := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (constgen_N_0 : Int),
  ((¬(constgen_N_0 > 0)) ->
   ((k0 0 constgen_N_0))) ∧
  ((constgen_N_0 > 0) ->
   ((0 < constgen_N_0)) ∧
   ((0 < constgen_N_0) ->
    ∀ (arr_elem₀ : Int),
     ((k0 (0 + arr_elem₀) constgen_N_0)))
   ) ∧
  (∀ (res₀ : Int),
   ((k0 res₀ constgen_N_0)) ->
    (constgen_N_0 > 1) ->
     (1 < constgen_N_0))
  
end F
