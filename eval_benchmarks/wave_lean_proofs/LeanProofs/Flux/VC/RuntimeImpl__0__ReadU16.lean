import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TypesVmCtx
import LeanProofs.Flux.Struct.TypesFdMap
import LeanProofs.Flux.Fun.TypesLINEARMEMSIZE
import LeanProofs.Flux.Fun.TypesTWOPOWER20
open Classical
set_option linter.unusedVariables false


namespace F



def RuntimeImpl__0__ReadU16 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, 
 ∀ (cnt₀ : Int),
  ∀ (self₀ : TypesVmCtx),
   ((0 ≤ cnt₀) ∧ (2 ≤ (2 + cnt₀)) ∧ ((2 + cnt₀) < (0 + types_LINEAR_MEM_SIZE))) ->
    (cnt₀ ≥ 0) ->
     ((TypesVmCtx.base self₀) ≥ 0) ->
      (types_LINEAR_MEM_SIZE ≥ 0) ->
       ∀ (a'₂ : TypesFdMap),
        ((TypesVmCtx.arg_buf self₀) < types_TWO_POWER_20) ->
         ((TypesVmCtx.env_buf self₀) < types_TWO_POWER_20) ->
          ∀ (v₀ : Int),
           (v₀ < 1024) ->
            (v₀ ≥ 0) ->
             ∀ (v₁ : Int),
              (v₁ < 1024) ->
               (v₁ ≥ 0) ->
                ((cnt₀ < types_LINEAR_MEM_SIZE)) ∧
                (∀ (a'₅ : Int),
                 ((k0 a'₅ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₂) (TypesFdMap.counter a'₂) v₀ v₁))) ∧
                (∀ (a'₆ : Int),
                 ((k0 a'₆ cnt₀ (TypesVmCtx.arg_buf self₀) (TypesVmCtx.env_buf self₀) (TypesVmCtx.base self₀) (TypesVmCtx.homedir_host_fd self₀) (TypesVmCtx.net self₀) (TypesFdMap.reserve_len a'₂) (TypesFdMap.counter a'₂) v₀ v₁)) ->
                  (a'₆ ≥ 0) ->
                   ((0 ≤ (cnt₀ + 1))) ∧
                   (((cnt₀ + 1) < types_LINEAR_MEM_SIZE))
                   )
                
end F
