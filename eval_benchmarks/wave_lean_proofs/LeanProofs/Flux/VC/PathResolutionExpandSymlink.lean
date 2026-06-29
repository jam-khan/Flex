import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.TcbPathFOwnedComponents
open Classical
set_option linter.unusedVariables false


namespace F



def PathResolutionExpandSymlink := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, 
 ∀ (linkpath_components₀ : TcbPathFOwnedComponents),
  ∀ (dirfd₀ : Int),
   (((k0 0 (TcbPathFOwnedComponents.size linkpath_components₀) (TcbPathFOwnedComponents.ns_prefix linkpath_components₀) (TcbPathFOwnedComponents.depth linkpath_components₀) (TcbPathFOwnedComponents.is_relative linkpath_components₀) dirfd₀))) ∧
   (∀ (idx₀ : Int),
    ((k0 idx₀ (TcbPathFOwnedComponents.size linkpath_components₀) (TcbPathFOwnedComponents.ns_prefix linkpath_components₀) (TcbPathFOwnedComponents.depth linkpath_components₀) (TcbPathFOwnedComponents.is_relative linkpath_components₀) dirfd₀)) ->
     ((TcbPathFOwnedComponents.size linkpath_components₀) ≥ 0) ->
      (idx₀ < (TcbPathFOwnedComponents.size linkpath_components₀)) ->
       ∀ (num_symlinks₀ : Int),
        (¬(num_symlinks₀ ≥ 10)) ->
         ((0 ≤ idx₀)) ∧
         (∀ (a'₄ : TcbPathFOwnedComponents),
          ((k1 (TcbPathFOwnedComponents.size linkpath_components₀) (TcbPathFOwnedComponents.ns_prefix linkpath_components₀) (TcbPathFOwnedComponents.depth linkpath_components₀) (TcbPathFOwnedComponents.is_relative linkpath_components₀) dirfd₀ idx₀ num_symlinks₀))) ∧
         (((k1 (TcbPathFOwnedComponents.size linkpath_components₀) (TcbPathFOwnedComponents.ns_prefix linkpath_components₀) (TcbPathFOwnedComponents.depth linkpath_components₀) (TcbPathFOwnedComponents.is_relative linkpath_components₀) dirfd₀ idx₀ num_symlinks₀))) ∧
         (((k1 (TcbPathFOwnedComponents.size linkpath_components₀) (TcbPathFOwnedComponents.ns_prefix linkpath_components₀) (TcbPathFOwnedComponents.depth linkpath_components₀) (TcbPathFOwnedComponents.is_relative linkpath_components₀) dirfd₀ idx₀ num_symlinks₀)) ->
          ((k0 (idx₀ + 1) (TcbPathFOwnedComponents.size linkpath_components₀) (TcbPathFOwnedComponents.ns_prefix linkpath_components₀) (TcbPathFOwnedComponents.depth linkpath_components₀) (TcbPathFOwnedComponents.is_relative linkpath_components₀) dirfd₀)))
         )
   
end F
