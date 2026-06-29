import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.AddrMatchesNetlistEntry
open Classical
set_option linter.unusedVariables false


namespace F



def TypesImpl__36__AddrInNetlist := 
 ∀ (net₀ : Int),
  ∀ (addr₀ : Int),
   ∀ (port₀ : Int),
    (addr₀ ≥ 0) ->
     (port₀ ≥ 0) ->
      ((¬(addr_matches_netlist_entry net₀ addr₀ port₀ 0)) ->
       ((¬(addr_matches_netlist_entry net₀ addr₀ port₀ 1)) ->
        ((¬(addr_matches_netlist_entry net₀ addr₀ port₀ 2)) ->
         ((¬(addr_matches_netlist_entry net₀ addr₀ port₀ 3)) ->
          (False = ((((addr_matches_netlist_entry net₀ addr₀ port₀ 0) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 1)) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 2)) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 3)))) ∧
         ((addr_matches_netlist_entry net₀ addr₀ port₀ 3) ->
          (True = ((((addr_matches_netlist_entry net₀ addr₀ port₀ 0) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 1)) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 2)) ∨ True)))
         ) ∧
        ((addr_matches_netlist_entry net₀ addr₀ port₀ 2) ->
         (True = ((((addr_matches_netlist_entry net₀ addr₀ port₀ 0) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 1)) ∨ True) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 3))))
        ) ∧
       ((addr_matches_netlist_entry net₀ addr₀ port₀ 1) ->
        (True = ((((addr_matches_netlist_entry net₀ addr₀ port₀ 0) ∨ True) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 2)) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 3))))
       ) ∧
      ((addr_matches_netlist_entry net₀ addr₀ port₀ 0) ->
       (True = (((True ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 1)) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 2)) ∨ (addr_matches_netlist_entry net₀ addr₀ port₀ 3))))
      
end F
