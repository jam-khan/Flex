import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TypesImpl__5__FromSyscallRet := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (ret₀ : Int),
  (ret₀ ≥ 0) ->
   ((0 ≤ ret₀)) ∧
   ((((k0 ret₀ ret₀))) ∧
   (∀ (a'₀ : Int),
    ((k0 a'₀ ret₀)) ->
     (a'₀ = ret₀))
   )
   
end F
